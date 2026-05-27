/-
  SystemVerilog Parser — Recursive descent for synthesizable RTL

  Supports: module with #(parameter), input/output/output reg, wire/reg,
  assign, always @(posedge)/always @*, if/else, case/casez,
  localparam, integer, for loops, generate if, (* attributes *),
  `ifdef/`endif preprocessing, multiple modules.
-/

import Tools.SVParser.AST
import Tools.SVParser.Lexer

open Tools.SVParser.AST
open Tools.SVParser.Lexer

namespace Tools.SVParser.Parser

-- ============================================================================
-- Preprocessor: strip `ifdef/`endif blocks (take the default/else branch)
-- and remove `timescale, `define, `default_nettype, (* attributes *)
-- ============================================================================

/-- QANARY: strip `function automatic ... endfunction` blocks.
    Walks line-by-line; when a line starts with `function`, drops every
    line up to and including `endfunction`. Conservative — any nested
    `function`/`endfunction` would confuse this; sv2v output doesn't nest. -/
private def stripFunctionDefs (input : String) : String := Id.run do
  let lines := input.splitOn "\n"
  let mut result : List String := []
  let mut inFunc := false
  for line in lines do
    let t := line.trimLeft
    if t.startsWith "function " || t.startsWith "function\t" || t.startsWith "function automatic" then
      inFunc := true
    else if inFunc && (t.startsWith "endfunction") then
      inFunc := false
    else if inFunc then
      pure ()  -- drop
    else
      result := result ++ [line]
  "\n".intercalate result

/-- QANARY: rewrite `sv2v_cast_NAME(expr)` → `(expr)`.
    sv2v emits these as width-cast helpers; after stripFunctionDefs the
    NAME has no definition, so we strip both the prefix and the identifier
    that follows, leaving the parenthesized argument. -/
private partial def rewriteSv2vCasts (input : String) : String := Id.run do
  let mut s := input
  let mut out := ""
  let mut cont := true
  while cont do
    match s.splitOn "sv2v_cast_" with
    | [only] => out := out ++ only; cont := false
    | before :: rest =>
      let after := "sv2v_cast_".intercalate rest
      -- Skip the identifier (alphanumeric/underscore chars after the prefix)
      let mut idx : Nat := 0
      let arr := after.toList
      let len := arr.length
      let chars := arr.toArray
      while idx < len && (chars[idx]!.isAlphanum || chars[idx]! == '_') do
        idx := idx + 1
      if idx < len && chars[idx]! == '(' then
        out := out ++ before
        s := (after.drop idx).toString
      else
        -- not a call site, preserve verbatim and continue
        out := out ++ before ++ "sv2v_cast_"
        s := after
    | [] => cont := false
  out

/-- QANARY (Gap U): last whitespace-delimited token of a string — the port
    name in a direction declaration such as `input wire [69:0] rnd_i`. -/
private def lastIdentToken (s : String) : String :=
  ((s.replace "\t" " ").splitOn " ").filter (· ≠ "") |>.getLastD ""

/-- QANARY (Gap U): fold a Verilog-1995 non-ANSI port list into ANSI form.
    sv2v 0.0.13 emits `module M (\n  name,\n  ...\n);` with `input`/`output`
    direction declarations in the module body. Sparkle's `parsePortList`
    requires the Verilog-2001 ANSI form (direction in the header), so the raw
    output fails with `expected 'inout'` at the first bare port name. This pass
    detects a bare-name header port list, collects the matching body direction
    declarations, rewrites the header to ANSI form, and drops the consumed body
    declarations. String→string; no AST change. No-op on already-ANSI headers
    and on input with no foldable module header (idempotent). -/
private def foldNonAnsiPorts (input : String) : String := Id.run do
  let lines := (input.splitOn "\n").toArray
  let n := lines.size
  -- 1. header-open line: trimmed `module <name> (` ending in '('
  let mut hOpen : Option Nat := none
  for i in [0:n] do
    if hOpen.isNone then
      let t := lines[i]!.trim
      if t.startsWith "module " && t.endsWith "(" then hOpen := some i
  let some ho := hOpen | return input
  -- 2. port-list close: first subsequent trimmed line starting with ')'
  let mut hClose : Option Nat := none
  for j in [ho+1:n] do
    if hClose.isNone then
      if (lines[j]!.trim).startsWith ")" then hClose := some j
  let some hc := hClose | return input
  -- 3. collect bare header port names; abort (no-op) if already ANSI
  let mut names : List String := []
  let mut isAnsi := false
  for k in [ho+1:hc] do
    let t0 := lines[k]!.trim
    let t := if t0.endsWith "," then (t0.dropRight 1).trim else t0
    if t == "" then pure ()
    else if t.startsWith "input" || t.startsWith "output" || t.startsWith "inout" then
      isAnsi := true
    else names := names ++ [t]
  if isAnsi || names.isEmpty then return input
  -- 4. scan body for matching `input/output/inout ... <name>;` declarations
  let mut declMap : List (String × String) := []
  let mut consumed : List Nat := []
  for b in [hc+1:n] do
    let t := lines[b]!.trim
    if (t.startsWith "input" || t.startsWith "output" || t.startsWith "inout") && t.endsWith ";" then
      let decl := (t.dropRight 1).trim
      let nm := lastIdentToken decl
      if names.contains nm then
        declMap := declMap ++ [(nm, decl)]
        consumed := consumed ++ [b]
  -- 5. require every header port to have a body direction decl; else no-op
  if !names.all (fun nm => (declMap.find? (·.1 == nm)).isSome) then return input
  -- 6. rebuild: header in ANSI port order, then body minus consumed decls
  let ansiDecls := names.filterMap (fun nm => (declMap.find? (·.1 == nm)).map (·.2))
  let mut out : List String := []
  for i in [0:ho+1] do out := out ++ [lines[i]!]
  let dn := ansiDecls.length
  for idx in [0:dn] do
    out := out ++ ["\t" ++ ansiDecls[idx]! ++ (if idx + 1 < dn then "," else "")]
  out := out ++ [");"]
  for b in [hc+1:n] do
    if !consumed.contains b then out := out ++ [lines[b]!]
  return "\n".intercalate out

/-- Simple preprocessor: remove ifdef blocks (keeping else branch),
    strip `timescale/`define/`default_nettype directives and (* ... *) attributes -/
def preprocess (input : String) : String := Id.run do
  -- QANARY (Gap U): fold Verilog-1995 non-ANSI port lists into ANSI form
  -- before any other transformation, so parsePortList sees direction-in-header.
  let input := foldNonAnsiPorts input
  -- QANARY: normalize `@(*)` → `@*` BEFORE attribute-stripping. The
  -- `removeAttributes` helper greedily matches `(* ... *)` including
  -- the `(*` inside `@(*)`, which would silently corrupt the always-block
  -- to `@` (followed by whatever the line continues with). Doing the
  -- substitution up front avoids the collision. Original substitution
  -- at end of function preserved as a defense in depth for tools that
  -- emit the form differently.
  let input := "@*".intercalate (input.splitOn "@(*)")
  -- QANARY: strip `function automatic ... endfunction` blocks. sv2v emits
  -- these for SystemVerilog width casts (`sv2v_cast_NAME(expr)`). For our
  -- purposes — formal verification of arithmetic invariants — the casts
  -- are width-adjusting no-ops and can be safely removed by replacing the
  -- call site with the bare expression. Function definitions are dropped
  -- entirely; call sites get rewritten by the next pass.
  let input := stripFunctionDefs input
  -- QANARY: rewrite `sv2v_cast_NAME(expr)` → `(expr)`. After def-stripping
  -- the names are dangling references; this pass replaces them with their
  -- argument, which is semantically equivalent for width-cast helpers.
  let input := rewriteSv2vCasts input
  let lines := input.splitOn "\n"
  let mut result : List String := []
  let mut ifdefDepth : Nat := 0
  let mut skipDepth : Nat := 0  -- depth at which we started skipping (0 = not skipping)
  for line in lines do
    let trimmed := line.trimLeft
    if trimmed.startsWith "`ifdef" then
      ifdefDepth := ifdefDepth + 1
      if skipDepth == 0 then
        -- `ifdef X: macros are not defined, skip this branch
        skipDepth := ifdefDepth
    else if trimmed.startsWith "`ifndef" then
      ifdefDepth := ifdefDepth + 1
      -- `ifndef X: macros are not defined, KEEP this branch (don't skip)
    else if trimmed.startsWith "`elsif" then
      if skipDepth == ifdefDepth then
        -- Was skipping this level: check elsif (treat as still skipping for simplicity)
        pure ()
      else if skipDepth == 0 then
        -- Was not skipping: now start skipping (elsif branch of a kept ifndef)
        skipDepth := ifdefDepth
    else if trimmed.startsWith "`else" then
      if skipDepth == ifdefDepth then
        skipDepth := 0  -- Was skipping: take the else branch
      else if skipDepth == 0 then
        skipDepth := ifdefDepth  -- Was keeping: skip the else branch
    else if trimmed.startsWith "`endif" then
      if skipDepth == ifdefDepth then
        skipDepth := 0
      if ifdefDepth > 0 then ifdefDepth := ifdefDepth - 1
    else if skipDepth > 0 then
      pure ()  -- skip this line
    else if trimmed.startsWith "`timescale" || trimmed.startsWith "`define" ||
            trimmed.startsWith "`default_nettype" ||
            trimmed.startsWith "`PICORV32" ||
            trimmed.startsWith "`assert" then
      pure ()  -- skip directive / macro invocation
    else if trimmed.startsWith "`debug" then
      -- Replace debug macro with empty statement (semicolon)
      result := result ++ [";"]
    else
      -- Remove (* ... *) attributes
      let cleaned := removeAttributes line
      result := result ++ [cleaned]
  -- Replace @(*) with @* (LiteX/Migen outputs @(*) which is equivalent)
  let joined := "\n".intercalate result
  "@*".intercalate (joined.splitOn "@(*)")
where
  removeAttributes (s : String) : String := Id.run do
    let mut result := s
    -- Remove (* ... *) attributes
    let mut cont := true
    while cont do
      match result.splitOn "(*" with
      | [_] => cont := false
      | before :: rest =>
        let afterStar := "*".intercalate rest
        match afterStar.splitOn "*)" with
        | _ :: after => result := before ++ " ".intercalate after
        | [] => cont := false
      | [] => cont := false
    -- Remove inline `MACRONAME (backtick macros used as modifiers)
    result := result.replace "`FORMAL_KEEP " ""
    result := result.replace "`FORMAL_KEEP" ""
    result

-- ============================================================================
-- Expression parsing (all mutually recursive)
-- ============================================================================

mutual

partial def parseExpr : P SVExpr := parseTernary

partial def parseTernary : P SVExpr := do
  let e ← parseLogOr
  match ← attempt qmark with
  | some _ => let t ← parseExpr; colon; let el ← parseExpr; pure (SVExpr.ternary e t el)
  | none => pure e

partial def parseLogOr : P SVExpr := do
  let mut e ← parseLogAnd
  let mut cont := true
  while cont do
    match ← attempt (op2 "||") with
    | some _ => let rhs ← parseLogAnd; e := SVExpr.binary .logOr e rhs
    | none => cont := false
  pure e

partial def parseLogAnd : P SVExpr := do
  let mut e ← parseBitOr
  let mut cont := true
  while cont do
    match ← attempt (op2 "&&") with
    | some _ => let rhs ← parseBitOr; e := SVExpr.binary .logAnd e rhs
    | none => cont := false
  pure e

partial def parseBitOr : P SVExpr := do
  let mut e ← parseBitXor
  let mut cont := true
  while cont do
    match ← attempt (do
      let _ ← token (matchStr "|")
      let next ← peekChar
      if next == some '|' then fail "||"
      pure ()) with
    | some _ => let rhs ← parseBitXor; e := SVExpr.binary .bitOr e rhs
    | none => cont := false
  pure e

partial def parseBitXor : P SVExpr := do
  let mut e ← parseBitAnd
  let mut cont := true
  while cont do
    match ← attempt (token (matchStr "^")) with
    | some _ => let rhs ← parseBitAnd; e := SVExpr.binary .bitXor e rhs
    | none => cont := false
  pure e

partial def parseBitAnd : P SVExpr := do
  let mut e ← parseEquality
  let mut cont := true
  while cont do
    match ← attempt (do
      let _ ← token (matchStr "&")
      let next ← peekChar
      if next == some '&' then fail "&&"
      pure ()) with
    | some _ => let rhs ← parseEquality; e := SVExpr.binary .bitAnd e rhs
    | none => cont := false
  pure e

partial def parseEquality : P SVExpr := do
  let mut e ← parseRelational
  let mut cont := true
  while cont do
    match ← attempt (op2 "!=") with
    | some _ => let rhs ← parseRelational; e := SVExpr.binary .neq e rhs
    | none =>
      match ← attempt (op2 "==") with
      | some _ => let rhs ← parseRelational; e := SVExpr.binary .eq e rhs
      | none => cont := false
  pure e

partial def parseRelational : P SVExpr := do
  let mut e ← parseShift
  let mut cont := true
  while cont do
    match ← attempt (op2 "<=") with
    | some _ => let rhs ← parseShift; e := SVExpr.binary .le e rhs
    | none =>
      match ← attempt (op2 ">=") with
      | some _ => let rhs ← parseShift; e := SVExpr.binary .ge e rhs
      | none =>
        match ← attempt (do let _ ← token (matchStr "<"); let next ← peekChar
                            if next == some '<' then fail "<<"; pure ()) with
        | some _ => let rhs ← parseShift; e := SVExpr.binary .lt e rhs
        | none =>
          match ← attempt (do let _ ← token (matchStr ">"); let next ← peekChar
                              if next == some '>' then fail ">>"; pure ()) with
          | some _ => let rhs ← parseShift; e := SVExpr.binary .gt e rhs
          | none => cont := false
  pure e

partial def parseShift : P SVExpr := do
  let mut e ← parseAdd
  let mut cont := true
  while cont do
    match ← attempt (op2 ">>>") with
    | some _ => let rhs ← parseAdd; e := SVExpr.binary .asr e rhs
    | none =>
      match ← attempt (op2 "<<") with
      | some _ => let rhs ← parseAdd; e := SVExpr.binary .shl e rhs
      | none =>
        match ← attempt (op2 ">>") with
        | some _ => let rhs ← parseAdd; e := SVExpr.binary .shr e rhs
        | none => cont := false
  pure e

partial def parseAdd : P SVExpr := do
  let mut e ← parseMul
  let mut cont := true
  while cont do
    -- Attempt-wrap both `+` and `-` consumption together with their parseMul
    -- so the operator consumption rolls back if no RHS expression follows
    -- (e.g., when the `+` belongs to a trailing `+:` part-select separator).
    match ← attempt (do let _ ← token (matchStr "+"); parseMul) with
    | some rhs => e := SVExpr.binary .add e rhs
    | none =>
      match ← attempt (do let _ ← token (matchStr "-"); parseMul) with
      | some rhs => e := SVExpr.binary .sub e rhs
      | none => cont := false
  pure e

partial def parseMul : P SVExpr := do
  let mut e ← parseUnary
  let mut cont := true
  while cont do
    match ← attempt (token (matchStr "*")) with
    | some _ => let rhs ← parseUnary; e := SVExpr.binary .mul e rhs
    | none =>
      match ← attempt (token (matchStr "/")) with
      | some _ => let rhs ← parseUnary; e := SVExpr.binary .div e rhs
      | none =>
        match ← attempt (token (matchStr "%")) with
        | some _ => let rhs ← parseUnary; e := SVExpr.binary .mod e rhs
        | none => cont := false
  pure e

partial def parseUnary : P SVExpr := do
  let c ← peekChar
  match c with
  | some '!' => let _ ← token (matchStr "!"); let e ← parseUnary; pure (SVExpr.unary .logNot e)
  | some '~' => let _ ← token (matchStr "~"); let e ← parseUnary; pure (SVExpr.unary .bitNot e)
  | some '-' =>
    -- Unary minus: -expr (two's complement negation)
    match ← attempt (do let _ ← token (matchStr "-"); let e ← parseUnary; pure e) with
    | some e => pure (SVExpr.unary .neg e)
    | none => parsePrimary
  | some '&' =>
    -- Check for reduction AND (unary &) vs binary &
    match ← attempt (do
      let _ ← token (matchStr "&")
      let next ← peekChar
      if next == some '&' then fail "&&"
      let e ← parseUnary; pure e) with
    | some e => pure (SVExpr.unary .reductAnd e)
    | none => parsePrimaryPost
  | some '|' =>
    match ← attempt (do
      let _ ← token (matchStr "|")
      let next ← peekChar
      if next == some '|' then fail "||"
      let e ← parseUnary; pure e) with
    | some e => pure (SVExpr.unary .reductOr e)
    | none => parsePrimaryPost
  | _ => parsePrimaryPost

partial def parsePrimaryPost : P SVExpr := do
  let e ← parsePrimary
  parsePostfix e

partial def parsePostfix (e : SVExpr) : P SVExpr := do
  match ← attempt lbracket with
  | some _ =>
    -- Try [base +: width] part-select first (IEEE 1800-2017 §11.5.1).
    -- Use parseExpr for both BASE and WIDTH (compound expressions per IEEE);
    -- the `attempt` rolls back if the trailing `+:` doesn't match. Safety of
    -- parseExpr here relies on parseAdd's `+` consumption being attempt-wrapped
    -- (mirrors the `-` arm) so parseExpr stops cleanly at the `+:` separator.
    match ← attempt (do
      let base ← parseExpr
      let _ ← token (matchStr "+:")
      let widthExpr ← parseExpr
      rbracket
      pure (base, widthExpr)
    ) with
    | some (base, widthExpr) => parsePostfix (SVExpr.partSelectPlus e base widthExpr)
    | none =>
    -- Try [base -: width] descending part-select (IEEE 1800-2017 §11.5.1)
    match ← attempt (do
      let base ← parseExpr
      let _ ← token (matchStr "-:")
      let widthExpr ← parseExpr
      rbracket
      pure (base, widthExpr)
    ) with
    | some (base, widthExpr) => parsePostfix (SVExpr.partSelectMinus e base widthExpr)
    | none =>
    -- Normal: [idx], [hi:lo]
    let idx ← parseExpr
    match ← attempt colon with
    | some _ =>
      let lo ← parseExpr
      rbracket
      match idx, lo with
      | .lit (.decimal _ hi), .lit (.decimal _ lo') => parsePostfix (SVExpr.slice e hi lo')
      | .lit (.hex _ hi), .lit (.decimal _ lo') => parsePostfix (SVExpr.slice e hi lo')
      | _, _ => parsePostfix (SVExpr.slice e 0 0)
    | none =>
      rbracket
      parsePostfix (SVExpr.index e idx)
  | none => pure e

partial def parsePrimary : P SVExpr := do
  let c ← peekChar
  match c with
  | some '{' =>
    lbrace
    let first ← parseExpr
    -- Check for replication: {n{expr}}
    match ← attempt lbrace with
    | some _ =>
      let inner ← parseExpr; rbrace; rbrace
      pure (SVExpr.repeat_ first inner)
    | none =>
      let mut args := [first]
      let mut cont := true
      while cont do
        match ← attempt comma with
        | some _ => let e ← parseExpr; args := args ++ [e]
        | none => cont := false
      rbrace; pure (SVExpr.concat args)
  | some '(' => lparen; let e ← parseExpr; rparen; pure e
  | some '"' =>
    -- String literal: "text" → treat as constant 0 (debug strings not synthesizable)
    let _ ← nextChar  -- consume opening "
    let mut running := true
    while running do
      let ch ← nextChar
      if ch == '"' then running := false
    ws
    pure (SVExpr.lit (.decimal none 0))
  | some '$' =>
    -- System functions like $signed, $unsigned
    let _ ← nextChar  -- consume $
    let name ← identifier
    lparen; let arg ← parseExpr; rparen
    if name == "signed" then
      -- Apply $signed to concat and slice expressions (known sub-32-bit width)
      -- Identity for full-width wire references (already 32-bit)
      match arg with
      | .concat _ => pure (SVExpr.unary .signed arg)
      | .slice _ _ _ => pure (SVExpr.unary .signed arg)
      | .index _ _ => pure (SVExpr.unary .signed arg)
      | _ => pure arg
    else
      pure arg
  | some '\'' =>
    -- Unsized literal: 'b0, 'bx, 'h0, etc.
    let _ ← token (matchStr "'")
    -- IEEE 1800-2017 §5.7.1: optional signed marker `s`/`S` between apostrophe and base.
    -- Parse-only coverage (Path A — drop signedness); mirrors Lexer.lean::numericLiteral.
    let _ ← attempt (do
      match (← peekChar) with
      | some 's' | some 'S' => let _ ← nextChar
      | _ => fail "no signed marker")
    let base ← nextChar
    match base with
    | 'b' | 'B' =>
      skipUnderscoresAndSpaces
      let bd ← binDigitsStr
      pure (SVExpr.lit (.binary none (binToNat bd)))
    | 'h' | 'H' =>
      skipUnderscoresAndSpaces
      let hd ← hexDigitsWithUnderscore
      pure (SVExpr.lit (.hex none (hexToNat hd)))
    | 'd' | 'D' =>
      skipUnderscoresAndSpaces
      let dd ← digits
      pure (SVExpr.lit (.decimal none dd.toNat!))
    | 'o' | 'O' =>
      -- IEEE 1800-2017 §5.7.1: octal base; parallel to Lexer.lean::numericLiteral patch.
      skipUnderscoresAndSpaces
      let od ← octDigitsStr
      pure (SVExpr.lit (.decimal none (octToNat od)))
    | _ => fail s!"unexpected base '{base}' in unsized literal"
  | some c' =>
    if isDigit c' then let lit ← numericLiteral; pure (SVExpr.lit lit)
    else if isAlpha c' then let name ← identifier; pure (SVExpr.ident name)
    else fail s!"unexpected char in expression: '{c'}'"
  | none => fail "unexpected end of input in expression"

-- Statement parsing
partial def parseStmtList : P (List SVStmt) := do
  match ← attempt (keyword "begin") with
  | some _ =>
    let _ ← attempt (do colon; let _ ← identifier; pure ())
    -- Gap Y (Track ii): mirror parseAlwaysBody's depth-tracked error-recovery
    -- loop so a block-local declaration (e.g. sv2v's `reg signed [31:0] i;` loop
    -- counter) inside an if/case/for branch is skipped rather than hard-failing
    -- `keyword "end"`. parseStmt has no local-decl arm; the always-body path
    -- already tolerates this via token-skip recovery — this brings the
    -- branch-body path (parseStmtList) in line. (CITE: parseAlwaysBody :771.)
    let mut stmts : List SVStmt := []
    let mut depth : Nat := 1
    while depth > 0 do
      match ← attempt parseStmt with
      | some s => stmts := stmts ++ [s]
      | none =>
        match ← attempt (keyword "end") with
        | some _ => depth := depth - 1
        | none =>
          match ← attempt (keyword "begin") with
          | some _ => depth := depth + 1
          | none => let _ ← nextChar
    pure stmts
  | none =>
    -- Single statement or empty (;)
    match ← attempt semi with
    | some _ => pure []  -- empty statement
    | none => let s ← parseStmt; pure [s]

partial def parseStmt : P SVStmt := do
  -- Empty statement (standalone ;)
  match ← attempt semi with
  | some _ => return SVStmt.blockAssign (.lit (.decimal none 0)) (.lit (.decimal none 0))
  | none => pure ()
  match ← attempt (keyword "if") with
  | some _ =>
    lparen; let cond ← parseExpr; rparen
    let thenB ← parseStmtList
    let elseB ← match ← attempt (keyword "else") with
      | some _ => parseStmtList | none => pure []
    pure (SVStmt.ifElse cond thenB elseB)
  | none =>
    match ← attempt (keyword "case") with
    | some _ => parseCaseBody
    | none =>
      match ← attempt (keyword "casez") with
      | some _ => parseCaseBody
      | none =>
        match ← attempt (keyword "for") with
        | some _ =>
          lparen
          let init ← parseAssignStmt
          let cond ← parseExpr; semi
          let step ← parseAssignStmtNoSemi
          rparen
          let body ← parseStmtList
          pure (SVStmt.forLoop init cond step body)
        | none =>
          match ← attempt (keyword "assert") with
          | some _ =>
            lparen; let cond ← parseExpr; rparen; semi
            pure (SVStmt.assertStmt cond)
          | none => parseAssignStmt

partial def parseCaseBody : P SVStmt := do
  lparen; let expr ← parseExpr; rparen
  let mut arms : List (List SVExpr × List SVStmt) := []
  let mut default_ : Option (List SVStmt) := none
  let mut cont := true
  while cont do
    match ← attempt (keyword "endcase") with
    | some _ => cont := false
    | none =>
      match ← attempt (keyword "default") with
      | some _ =>
        colon; let stmts ← parseStmtList; default_ := some stmts
      | none =>
        -- Parse one or more comma-separated labels
        let first ← parseExpr
        let mut labels := [first]
        let mut moreLabels := true
        while moreLabels do
          match ← attempt comma with
          | some _ =>
            -- Check it's not a new case label (followed by :)
            match ← attempt (do let e ← parseExpr; pure e) with
            | some e => labels := labels ++ [e]
            | none => moreLabels := false
          | none => moreLabels := false
        colon
        let stmts ← parseStmtList
        arms := arms ++ [(labels, stmts)]
  pure (SVStmt.caseStmt expr arms default_)

partial def parseAssignStmt : P SVStmt := do
  -- Try non-blocking first: lhs <= expr ;
  match ← attempt (do
    let lhs ← parsePrimaryPost
    op2 "<="; let rhs ← parseExpr; semi
    pure (SVStmt.nonblockAssign lhs rhs)) with
  | some s => pure s
  | none =>
    let lhs ← parsePrimaryPost
    eqSign; let rhs ← parseExpr; semi
    pure (SVStmt.blockAssign lhs rhs)

partial def parseAssignStmtNoSemi : P SVStmt := do
  let lhs ← parsePrimaryPost
  eqSign; let rhs ← parseExpr
  pure (SVStmt.blockAssign lhs rhs)

end -- mutual

-- ============================================================================
-- Module-level parsing (not mutually recursive with expressions)
-- ============================================================================

def parsePortDir : P SVPortDir := do
  match ← attempt (keyword "input") with
  | some _ => pure .input
  | none => match ← attempt (keyword "output") with
    | some _ => pure .output
    | none => keyword "inout"; pure .inout

def parseOptWidth : P (Option (Nat × Nat)) := do
  match ← attempt bitRange with
  | some r => pure (some r) | none => pure none

/-- Parse `[hiExpr : loExpr]` using the full expression parser, NOT the
    skip-and-default-31 lexer fallback. Returns the SVExpr forms so
    `lowerModule` can re-evaluate them against folded paramVals.
    This is the Pivot 2 PoC option A2 entry point. -/
def parseOptWidthExpr : P (Option (SVExpr × SVExpr)) := do
  match ← attempt lbracket with
  | none => pure none
  | some _ =>
    let hi ← parseExpr
    colon
    let lo ← parseExpr
    rbracket
    pure (some (hi, lo))

/-- Parse a port: direction [reg] [width] name. Captures both the
    eagerly-evaluated literal width (back-compat) AND the SVExpr form
    of the bit range (used when paramVals are available, in lowerModule). -/
def parsePortInList : P SVPort := do
  let dir ← parsePortDir
  let isReg ← match ← attempt (keyword "reg") with | some _ => pure true | none => pure false
  let _ ← attempt (keyword "logic")
  let _ ← attempt (keyword "wire")
  let _ ← attempt (keyword "signed")
  -- Try the SVExpr-based bit-range first; if successful, derive a
  -- conservative literal pair (31:0 default) so existing back-compat
  -- consumers still see *some* width. lowerModule will override with
  -- the param-folded value.
  let widthExpr ← parseOptWidthExpr
  let width : Option (Nat × Nat) := widthExpr.map (fun _ => (31, 0))
  let name ← identifier
  pure { dir, isReg, width, widthExpr, name }

/-- Parse port list with direction carry-over.
    In Verilog, `input clk, resetn` means both are inputs.
    Direction/reg/width persist until a new direction keyword appears. -/
def parsePortList : P (List SVPort) := do
  lparen
  let first ← parsePortInList
  let mut ports := [first]
  let mut lastDir := first.dir
  let mut lastIsReg := first.isReg
  let mut lastWidth := first.width
  let mut lastWidthExpr := first.widthExpr
  let mut cont := true
  while cont do
    match ← attempt comma with
    | some _ =>
      -- Check if next token is a direction keyword
      match ← attempt parsePortDir with
      | some dir =>
        lastDir := dir
        lastIsReg := match ← attempt (keyword "reg") with | some _ => true | none => false
        let _ ← attempt (keyword "logic")
        let _ ← attempt (keyword "wire")
        let _ ← attempt (keyword "signed")
        let we ← parseOptWidthExpr
        lastWidthExpr := we
        lastWidth := we.map (fun _ => (31, 0))
        let name ← identifier
        let port := { dir := lastDir, isReg := lastIsReg, width := lastWidth,
                      widthExpr := lastWidthExpr, name : SVPort }
        ports := ports ++ [port]
      | none =>
        -- No direction keyword — carry over from previous
        let _ ← attempt (keyword "signed")
        -- Check for new width override (Pivot 2 PoC path)
        let we ← parseOptWidthExpr
        let widthExpr := if we.isSome then we else lastWidthExpr
        let width : Option (Nat × Nat) :=
          if we.isSome then some (31, 0) else lastWidth
        let name ← identifier
        let port := { dir := lastDir, isReg := lastIsReg, width, widthExpr, name : SVPort }
        ports := ports ++ [port]
    | none => cont := false
  rparen; pure ports

/-- Parse a single parameter declaration: parameter [width] name = value -/
def parseParamDecl (isLocal : Bool) : P SVParam := do
  let _ ← attempt (keyword "integer")  -- optional: integer type
  let _ ← attempt (keyword "signed")
  let width ← parseOptWidth
  let name ← identifier
  eqSign; let value ← parseExpr
  pure { name, width, value, isLocal }

/-- Parse parameter list in #(...) -/
def parseParamList : P (List SVParam) := do
  token (matchStr "#"); lparen
  let mut params : List SVParam := []
  let mut cont := true
  while cont do
    keyword "parameter"
    let p ← parseParamDecl false
    params := params ++ [p]
    match ← attempt comma with
    | some _ => pure ()
    | none => cont := false
  rparen
  pure params

def parseSensitivity : P SVSensitivity := do
  match ← attempt (keyword "posedge") with
  | some _ => let s ← identifier; pure (SVSensitivity.posedge s)
  | none => match ← attempt (keyword "negedge") with
    | some _ => let s ← identifier; pure (SVSensitivity.negedge s)
    | none => let _ ← token (matchStr "*"); pure SVSensitivity.star

partial def parseAlwaysBlock : P SVModuleItem := do
  keyword "always"
  let _ ← attempt (matchStr "_ff")
  let _ ← attempt (matchStr "_comb")
  ws
  match ← attempt at_ with
  | some _ =>
    -- Sensitivity list: @(posedge clk or negedge rst) or @*
    -- Note: @(*) is normalized to @* in preprocessing
    match ← attempt (do let _ ← token (matchStr "*"); pure ()) with
    | some _ =>
      -- always @* — try begin/end or single statement
      let body ← parseAlwaysBody
      pure (SVModuleItem.alwaysBlock .star body)
    | none =>
      lparen; let sens ← parseSensitivity
      let _ ← many (do keyword "or"; let _ ← parseSensitivity; pure ())
      rparen
      let body ← parseAlwaysBody
      pure (SVModuleItem.alwaysBlock sens body)
  | none =>
    -- always @* shorthand (without @)
    let body ← parseAlwaysBody
    pure (SVModuleItem.alwaysBlock .star body)
where
  parseAlwaysBody : P (List SVStmt) := do
    match ← attempt (keyword "begin") with
    | some _ =>
      let _ ← attempt (do colon; let _ ← identifier; pure ())
      -- Parse statements, tracking begin/end depth
      let mut stmts : List SVStmt := []
      let mut depth : Nat := 1  -- we already consumed one "begin"
      while depth > 0 do
        -- Try to parse a statement
        match ← attempt parseStmt with
        | some s =>
          stmts := stmts ++ [s]
          -- Count begin/end depth changes from the statement
          -- (parseStmt already consumed matching begin/end internally)
        | none =>
          -- Check for end keyword
          match ← attempt (keyword "end") with
          | some _ => depth := depth - 1
          | none =>
            -- Check for begin keyword (nested block we couldn't parse)
            match ← attempt (keyword "begin") with
            | some _ => depth := depth + 1
            | none =>
              -- Skip one token (error recovery)
              let _ ← nextChar
      pure stmts
    | none =>
      let s ← parseStmt; pure [s]

/-- Parse multiple comma-separated names: `reg [w] a, b, c;` → 3 items -/
def parseMultiNames (mkItem : String → SVModuleItem) : P (List SVModuleItem) := do
  let first ← identifier
  let mut items := [mkItem first]
  let mut cont := true
  while cont do
    match ← attempt comma with
    | some _ => let n ← identifier; items := items ++ [mkItem n]
    | none => cont := false
  semi; pure items

mutual

/-- Parse the items inside one branch of a generate if/else block.
    Collects items until we see `end` at depth 0. -/
partial def parseGenerateBranchItems : P (List SVModuleItem) := do
  keyword "begin"
  let mut items : List SVModuleItem := []
  let mut done := false
  while !done do
    match ← attempt (keyword "end") with
    | some _ => done := true
    | none =>
      match ← attempt parseModuleItems with
      | some itemGroup => items := items ++ itemGroup
      | none =>
        -- Skip unrecognized token
        let _ ← nextChar; pure ()
  pure items

/-- Parse a generate if/else if/else/endgenerate block.
    Returns generateBlock with condition, if-body, and else-body.
    Chained `else if` is represented by nesting: else-body contains another generateBlock. -/
partial def parseGenerateBlock : P (List SVModuleItem) := do
  -- Already consumed "generate" keyword
  -- Expect: if (COND) begin ... end [else [if (COND) begin ... end]* [begin ... end]] endgenerate
  keyword "if"
  lparen; let cond ← parseExpr; rparen
  let ifItems ← parseGenerateBranchItems
  -- Check for else / else if
  let elseItems ← match ← attempt (keyword "else") with
    | some _ =>
      match ← attempt (keyword "if") with
      | some _ =>
        -- else if: parse condition and branches, wrap as nested generateBlock
        lparen; let cond2 ← parseExpr; rparen
        let ifItems2 ← parseGenerateBranchItems
        let elseItems2 ← match ← attempt (keyword "else") with
          | some _ => parseGenerateBranchItems
          | none => pure []
        pure [SVModuleItem.generateBlock cond2 ifItems2 elseItems2]
      | none =>
        -- plain else
        parseGenerateBranchItems
    | none => pure []
  keyword "endgenerate"
  pure [SVModuleItem.generateBlock cond ifItems elseItems]

partial def parseModuleItems : P (List SVModuleItem) := do
  match ← attempt (keyword "assign") with
  | some _ =>
    let lhs ← parseExpr; eqSign; let rhs ← parseExpr; semi
    pure [SVModuleItem.contAssign lhs rhs]
  | none => match ← attempt (keyword "wire") with
    | some _ =>
      let _ ← attempt (keyword "signed")
      let w ← parseOptWidth
      let n ← identifier
      match ← attempt eqSign with
      | some _ => let e ← parseExpr; semi; pure [SVModuleItem.wireDecl n w (some e)]
      | none =>
        -- Check for additional comma-separated names
        let mut items := [SVModuleItem.wireDecl n w none]
        let mut cont := true
        while cont do
          match ← attempt comma with
          | some _ => let n2 ← identifier; items := items ++ [SVModuleItem.wireDecl n2 w none]
          | none => cont := false
        semi; pure items
    | none => match ← attempt (keyword "reg") with
      | some _ =>
        let _ ← attempt (keyword "signed")
        let w ← parseOptWidth; let n ← identifier
        match ← attempt lbracket with
        | some _ =>
          -- Array dimension: try [lo:hi] with numeric values
          let arrSize ← match ← attempt (do
            let lo ← token digits
            colon
            let hi ← token digits
            rbracket
            pure (hi.toNat! - lo.toNat! + 1)) with
          | some size => pure size
          | none =>
            -- Parameterized — skip until ]
            let mut depth : Nat := 1
            while depth > 0 do
              match ← attempt rbracket with
              | some _ => depth := depth - 1
              | none => match ← attempt lbracket with
                | some _ => depth := depth + 1
                | none => let _ ← nextChar; pure ()
            pure 32  -- default
          semi
          pure [SVModuleItem.regDecl n w (some arrSize)]
        | none =>
          -- Skip optional initializer: reg foo = expr;
          match ← attempt (token (matchStr "=")) with
          | some _ => let _ ← parseExpr; pure ()  -- consume init value
          | none => pure ()
          let mut items := [SVModuleItem.regDecl n w none]
          let mut cont := true
          while cont do
            match ← attempt comma with
            | some _ =>
              let n2 ← identifier
              match ← attempt (token (matchStr "=")) with
              | some _ => let _ ← parseExpr; pure ()
              | none => pure ()
              items := items ++ [SVModuleItem.regDecl n2 w none]
            | none => cont := false
          semi; pure items
      | none => match ← attempt (keyword "integer") with
        | some _ =>
          let items ← parseMultiNames (SVModuleItem.integerDecl ·)
          pure items
        | none => match ← attempt (keyword "localparam") with
          | some _ =>
            let p ← parseParamDecl true; semi; pure [SVModuleItem.paramDecl p]
          | none => match ← attempt (keyword "parameter") with
            | some _ =>
              let p ← parseParamDecl false; semi; pure [SVModuleItem.paramDecl p]
            | none => match ← attempt (keyword "generate") with
              | some _ => parseGenerateBlock
              | none => match ← attempt (keyword "initial") with
                | some _ =>
                  -- IEEE 1800-2017 §9.2.1:
                  --   initial_construct ::= 'initial' statement_or_null
                  -- Two grammatical forms accepted here:
                  --   `initial begin ... end`  — block form (this branch
                  --                              extracts $readmemh items
                  --                              for memory init; other
                  --                              statements are dropped).
                  --   `initial <single_stmt>;` — single-statement form
                  --                              (e.g., sv2v-emitted
                  --                              `initial _sv2v_0 = 0;`).
                  -- Initial blocks are non-synthesizable per §9.2; the parser
                  -- treats them as parse-time no-ops except for the
                  -- $readmemh memory-init affordance above.
                  match ← attempt (keyword "begin") with
                  | some _ =>
                    -- Block form: extract $readmemh; drop other statements.
                    let mut items : List SVModuleItem := []
                    let mut d : Nat := 1
                    while d > 0 do
                      -- Check for $readmemh("file", mem);
                      match ← attempt (do
                        let _ ← token (matchStr "$readmemh")
                        lparen
                        -- Parse filename string: "filename"
                        let _ ← token (matchStr "\"")
                        let mut filename : List Char := []
                        let mut readingName := true
                        while readingName do
                          let c ← nextChar
                          if c == '"' then readingName := false
                          else filename := filename ++ [c]
                        ws; comma
                        let memName ← identifier
                        rparen; semi
                        pure (String.ofList filename, memName)) with
                      | some (filename, memName) =>
                        items := items ++ [SVModuleItem.readmemh filename memName]
                      | none =>
                        let hitBegin ← attempt (keyword "begin")
                        if hitBegin.isSome then d := d + 1
                        else
                          let hitEnd ← attempt (keyword "end")
                          if hitEnd.isSome then d := d - 1
                          else let _ ← nextChar; pure ()
                    pure items
                  | none =>
                    -- Single-statement form (or empty `;`). Parse and drop —
                    -- synthesis-irrelevant per §9.2.
                    match ← attempt semi with
                    | some _ => pure []  -- empty statement: `initial ;`
                    | none =>
                      let _ ← parseStmt
                      pure []
                | none => match ← attempt (keyword "task") with
                | some _ =>
                  let n ← identifier; semi
                  -- Skip task body until endtask (tasks are not synthesizable)
                  let mut depth : Nat := 1
                  while depth > 0 do
                    match ← attempt (keyword "endtask") with
                    | some _ => depth := depth - 1
                    | none => let _ ← nextChar; pure ()
                  pure [SVModuleItem.taskDecl n []]
                | none =>
                  -- Try module instantiation: moduleName instName ( .port(expr), ... );
                  match ← attempt (do
                    let modName ← identifier
                    -- Parse optional #(.param(val), ...) parameter overrides
                    let mut paramOvr : List (String × SVExpr) := []
                    match ← attempt (token (matchStr "#")) with
                    | some _ =>
                      lparen
                      let mut pcont := true
                      while pcont do
                        match ← attempt (do dot; let pn ← identifier; lparen; let pe ← parseExpr; rparen; pure (pn, pe)) with
                        | some (pn, pe) =>
                          paramOvr := paramOvr ++ [(pn, pe)]
                          match ← attempt comma with | some _ => pure () | none => pcont := false
                        | none => pcont := false
                      rparen
                    | none => pure ()
                    let instName ← identifier
                    lparen
                    let mut conns : List (String × SVExpr) := []
                    let mut cont := true
                    while cont do
                      dot; let pName ← identifier; lparen; let pExpr ← parseExpr; rparen
                      conns := conns ++ [(pName, pExpr)]
                      match ← attempt comma with | some _ => pure () | none => cont := false
                    rparen; semi
                    pure (modName, instName, conns, paramOvr)
                  ) with
                  | some (modName, instName, conns, paramOvr) =>
                    pure [SVModuleItem.instantiation modName instName conns paramOvr]
                  | none =>
                  -- Try always block; on failure, skip balanced begin/end
                  match ← attempt parseAlwaysBlock with
                  | some item => pure [item]
                  | none =>
                    -- Skip past the always block by matching begin/end balance
                    keyword "always"
                    let _ ← attempt (matchStr "_ff")
                    let _ ← attempt (matchStr "_comb")
                    ws
                    let _ ← attempt at_
                    -- Skip sensitivity list
                    match ← attempt lparen with
                    | some _ =>
                      let mut parenDepth : Nat := 1
                      while parenDepth > 0 do
                        match ← attempt rparen with
                        | some _ => parenDepth := parenDepth - 1
                        | none => let _ ← nextChar; pure ()
                    | none =>
                      let _ ← attempt (token (matchStr "*"))
                    -- Skip body by matching begin/end
                    keyword "begin"
                    let mut depth : Nat := 1
                    while depth > 0 do
                      match ← attempt (keyword "begin") with
                      | some _ => depth := depth + 1
                      | none =>
                        match ← attempt (keyword "end") with
                        | some _ => depth := depth - 1
                        | none => let _ ← nextChar; pure ()
                    pure []

end  -- mutual

-- ============================================================================
-- Top-level module parsing
-- ============================================================================

partial def parseModule : P SVModule := do
  keyword "module"
  let name ← identifier
  -- Optional parameter list: #(parameter ...)
  let params ← match ← attempt (token (matchStr "#")) with
    | some _ =>
      lparen
      let mut ps : List SVParam := []
      let mut cont := true
      while cont do
        keyword "parameter"
        let p ← parseParamDecl false
        ps := ps ++ [p]
        match ← attempt comma with
        | some _ => pure ()
        | none => cont := false
      rparen; pure ps
    | none => pure []
  let ports ← parsePortList
  semi
  let itemGroups ← many parseModuleItems
  let items := itemGroups.toList.flatMap id
  keyword "endmodule"
  pure { name, params, ports, items }

-- ============================================================================
-- Public API
-- ============================================================================

def parse (input : String) : Except String SVDesign :=
  let preprocessed := preprocess input
  Lexer.run (do ws; let modules ← many1 parseModule; pure { modules := modules.toList }) preprocessed

def parseModuleFromString (input : String) : Except String SVModule :=
  let preprocessed := preprocess input
  Lexer.run (do ws; parseModule) preprocessed

end Tools.SVParser.Parser
