/-
  Verilog IR → Lean Semantic Model Generator

  Extracts a pure state-machine model from Sparkle IR (Module),
  generating Lean source code with State/Input/nextState definitions
  suitable for formal verification with `simp`, `omega`, `bv_decide`.

  Pipeline:
    Verilog → [SVParser] → IR Module → [extractModel] → SemanticModel → [generateLean] → .lean source
-/

import Sparkle.IR.AST
import Sparkle.IR.Type

open Sparkle.IR.AST
open Sparkle.IR.Type

namespace Tools.SVParser.Verify

-- ============================================================================
-- Semantic Model types
-- ============================================================================

/-- A register extracted from the IR -/
structure RegField where
  name : String
  width : Nat
  initValue : Int
  nextExpr : Expr
  deriving Repr

/-- An input port -/
structure InputField where
  name : String
  width : Nat
  deriving Repr

/-- Extracted semantic model of a hardware module -/
structure SemanticModel where
  moduleName : String
  registers : List RegField
  inputs : List InputField
  assertions : List (String × Expr) := []
  deriving Repr

-- ============================================================================
-- Model extraction from IR
-- ============================================================================

/-- Extract semantic model from an IR Module -/
def extractModel (m : Module) : SemanticModel :=
  let regs := m.body.filterMap fun stmt => match stmt with
    | .register name _clk _rst input initVal =>
      let width := match m.wires.find? (fun w => w.name == name) with
        | some p => p.ty.bitWidth
        | none => match m.outputs.find? (fun w => w.name == name) with
          | some p => p.ty.bitWidth
          | none => 32
      some { name, width, initValue := initVal, nextExpr := input }
    | _ => none
  -- Include rst as an input (it's used in mux conditions); only skip clk
  let inputs := m.inputs.filter (fun p => p.name != "clk")
    |>.map fun p => { name := p.name, width := p.ty.bitWidth : InputField }
  { moduleName := m.name, registers := regs, inputs := inputs
    assertions := m.assertions }

-- ============================================================================
-- Wire inlining (substitute assign references)
-- ============================================================================

/-- Build a map of wire name → expression from Stmt.assign -/
def collectAssigns (body : List Stmt) : List (String × Expr) :=
  body.filterMap fun stmt => match stmt with
    | .assign name rhs => some (name, rhs)
    | _ => none

/-- Recursively inline wire references with their definitions, tracking the
    active ref-resolution path in `visited` to cut genuine reference cycles.
    `regNames` lists register output names — those are NOT inlined (state,
    not wires). A name already on the active `visited` path is left symbolic
    instead of re-inlined: this terminates the self-referential assign
    `pk = {pk[hi:lo], ...}` that Lower.lean reconstructs for bit- or
    part-select LHS writes to a combinational body reg. Acyclic chains
    are unaffected
    (siblings each receive the same incoming `visited`). -/
partial def inlineAssignsGo (assigns : List (String × Expr))
    (visited : List String) : Expr → Expr
  | .ref name =>
    if visited.contains name then .ref name
    else
      match assigns.find? (·.1 == name) with
      | some (_, rhs) => inlineAssignsGo assigns (name :: visited) rhs
      | none => .ref name
  | .op operator args => .op operator (args.map (inlineAssignsGo assigns visited))
  | .concat args => .concat (args.map (inlineAssignsGo assigns visited))
  | .slice e hi lo => .slice (inlineAssignsGo assigns visited e) hi lo
  | .index a i => .index (inlineAssignsGo assigns visited a) (inlineAssignsGo assigns visited i)
  | e => e  -- const passes through

/-- Public entry point — original 2-arg signature preserved. Both call
    sites (`Verify.lean` `extractModel`, `Macro.lean:43`) invoke this
    `inlineAssigns assigns r.nextExpr` form **unchanged**. Seeds the
    cycle-tracking accumulator empty. -/
partial def inlineAssigns (assigns : List (String × Expr)) : Expr → Expr :=
  inlineAssignsGo assigns []

-- ============================================================================
-- Width inference
-- ============================================================================

/-- Infer the BitVec width of an IR expression -/
partial def inferWidth (regWidths inputWidths : List (String × Nat)) : Expr → Nat
  | .const _ w => w
  | .ref name =>
    match regWidths.find? (·.1 == name) with
    | some (_, w) => w
    | none => match inputWidths.find? (·.1 == name) with
      | some (_, w) => w
      | none => 32
  | .op .eq _ => 1
  | .op .lt_u _ => 1
  | .op .lt_s _ => 1
  | .op .le_u _ => 1
  | .op .le_s _ => 1
  | .op .gt_u _ => 1
  | .op .gt_s _ => 1
  | .op .ge_u _ => 1
  | .op .ge_s _ => 1
  | .op .mux args => match args with
    | [_, t, _] => inferWidth regWidths inputWidths t
    | _ => 32
  | .op _ args => match args with
    | a :: _ => inferWidth regWidths inputWidths a
    | _ => 32
  | .slice _ hi lo => hi - lo + 1
  | .concat args => args.foldl (fun acc a => acc + inferWidth regWidths inputWidths a) 0
  | .index _ _ => 32

-- ============================================================================
-- IR Expr → Lean source string
-- ============================================================================

/-- Sanitize a name for Lean (replace special chars) -/
def leanName (s : String) : String :=
  s.map fun c => if c == '$' || c == '.' then '_' else c

/-- Fix constant widths to match the target register width.
    Verilog unsized constants default to 32-bit in the IR, but the register
    may be 8-bit. Replace `Expr.const v 32` with `Expr.const v targetWidth`
    when the constant is used in a context where targetWidth is known. -/
partial def fixConstWidths (expr : Expr) (targetWidth : Nat)
    (widthEnv : List (String × Nat)) : Expr :=
  match expr with
  -- Widen a constant to the target width when it is the default unsized-32
  -- literal in a non-32 context (first disjunct = the original predicate
  -- verbatim, preserving every prior narrowing/widening), OR when it is
  -- narrower than the target (second disjunct = small-width signed/unsigned
  -- literals such as `1'sb0` → `.const 0 1`, which must widen to the register
  -- width). The first disjunct keeps `32 → narrower` resizing intact.
  | .const v w => if (w == 32 && targetWidth != 32) || (w < targetWidth) then .const v targetWidth else expr
  | .op .mux [c, t, e] =>
    .op .mux [c, fixConstWidths t targetWidth widthEnv, fixConstWidths e targetWidth widthEnv]
  | .op op args => .op op (args.map (fixConstWidths · targetWidth widthEnv))
  -- Thread each element's OWN inferred width (mirroring the `.slice` arm
  -- below) rather than the parent register width: a concat's elements have
  -- independent widths summing to the register width, so passing the parent
  -- width over-widens every slot.
  | .concat args => .concat (args.map (fun a => fixConstWidths a (inferWidth widthEnv widthEnv a) widthEnv))
  | .slice e hi lo => .slice (fixConstWidths e (hi - lo + 1) widthEnv) hi lo
  | _ => expr

/-- Coerce `e` (inferred width `fromW`) up to width `toW` (`toW ≥ fromW`).
    A const is relabelled; any other expr is zero-extended via
    `concat [const 0 (toW-fromW), e]` (high-zero ++ value), which `inferWidth`
    (:136) and `irExprToLean` (:242) already handle. Zero-extension is the
    correct Verilog widening for unsigned bitwise operands. -/
def widenExprTo (e : Expr) (fromW toW : Nat) : Expr :=
  if toW <= fromW then e else
  match e with
  | .const v _ => .const v toW
  | _          => .concat [.const 0 (toW - fromW), e]

/-- Fix constant widths by inferring the correct width from context.
    For binary ops, constants adopt the width of the other operand.
    For mux, constants adopt the width of the then-branch. -/
partial def fixConstWidthsSmart (expr : Expr) (widthEnv : List (String × Nat)) : Expr :=
  match expr with
  | .op .mux [c, t, e] =>
    let tc := fixConstWidthsSmart c widthEnv
    let tt := fixConstWidthsSmart t widthEnv
    let te := fixConstWidthsSmart e widthEnv
    let tw := inferWidth widthEnv widthEnv tt
    -- Fix else-branch constants to match then-branch width
    let te := match te with
      | .const v 32 => if tw != 32 then .const v tw else te
      | _ => te
    .op .mux [tc, tt, te]
  | .op .eq [a, b] =>
    let a := fixConstWidthsSmart a widthEnv
    let b := fixConstWidthsSmart b widthEnv
    let wa := inferWidth widthEnv widthEnv a
    let wb := inferWidth widthEnv widthEnv b
    let a := if wa == 32 && wb != 32 then match a with | .const v _ => .const v wb | _ => a else a
    let b := if wb == 32 && wa != 32 then match b with | .const v _ => .const v wa | _ => b else b
    .op .eq [a, b]
  | .op op [a, b] =>
    let a := fixConstWidthsSmart a widthEnv
    let b := fixConstWidthsSmart b widthEnv
    let wa := inferWidth widthEnv widthEnv a
    let wb := inferWidth widthEnv widthEnv b
    let a := if wa == 32 && wb != 32 then match a with | .const v _ => .const v wb | _ => a else a
    let b := if wb == 32 && wa != 32 then match b with | .const v _ => .const v wa | _ => b else b
    -- gap #2 (narrow-reg-bitwrite): equal-width bitwise ops (and/or/xor) need
    -- both operands the same width. The const-32 reconcile above cannot fix a
    -- residual NON-32 mismatch (e.g. a 1-bit bit-select RHS meeting the RMW's
    -- reg-width-widened 1-bit mask). Equalize by coercing the narrower operand
    -- to the wider width (const → relabel; non-const → zero-extend via concat).
    let needsEqWidth := match op with | .and | .or | .xor => true | _ => false
    let (a, b) :=
      if needsEqWidth then
        let wa' := inferWidth widthEnv widthEnv a
        let wb' := inferWidth widthEnv widthEnv b
        if wa' < wb' then (widenExprTo a wa' wb', b)
        else if wb' < wa' then (a, widenExprTo b wb' wa')
        else (a, b)
      else (a, b)
    .op op [a, b]
  | .op op args => .op op (args.map (fixConstWidthsSmart · widthEnv))
  | .slice e hi lo => .slice (fixConstWidthsSmart e widthEnv) hi lo
  | .concat args => .concat (args.map (fixConstWidthsSmart · widthEnv))
  | _ => expr

/-- Convert IR Expr to a Lean BitVec expression string.
    `regNames`/`inputNames` control `s.` vs `i.` prefix.
    `widthEnv` is used for width inference (may include extra wires). -/
partial def irExprToLean (expr : Expr) (regNames inputNames : List (String × Nat))
    (widthEnv : List (String × Nat)) (stateVar inputVar : String) : String :=
  let go (e : Expr) := irExprToLean e regNames inputNames widthEnv stateVar inputVar
  let width := inferWidth widthEnv widthEnv expr
  match expr with
  | .const v w =>
    if v < 0 then s!"(BitVec.ofInt {w} ({v}))"
    else s!"({v}#{ w})"
  | .ref name =>
    if regNames.any (·.1 == name) then s!"{stateVar}.{leanName name}"
    else if inputNames.any (·.1 == name) then s!"{inputVar}.{leanName name}"
    else s!"{leanName name}"
  | .op .mux [cond, thenVal, elseVal] =>
    let condW := inferWidth widthEnv widthEnv cond
    s!"(if {go cond} != (0 : BitVec {condW}) then {go thenVal} else {go elseVal})"
  | .op .add [a, b] => s!"({go a} + {go b})"
  | .op .sub [a, b] => s!"({go a} - {go b})"
  | .op .mul [a, b] => s!"({go a} * {go b})"
  | .op .and [a, b] => s!"({go a} &&& {go b})"
  | .op .or [a, b] => s!"({go a} ||| {go b})"
  | .op .xor [a, b] => s!"({go a} ^^^ {go b})"
  | .op .not [a] =>
    if width <= 1 then s!"(if {go a} == (0 : BitVec {width}) then (1 : BitVec {width}) else (0 : BitVec {width}))"
    else s!"(~~~ {go a})"
  | .op .eq [a, b] =>
    s!"(if {go a} == {go b} then (1 : BitVec 1) else (0 : BitVec 1))"
  | .op .lt_u [a, b] => s!"(if {go a} < {go b} then (1 : BitVec 1) else (0 : BitVec 1))"
  | .op .shl [a, b] => s!"({go a} <<< {go b})"
  | .op .shr [a, b] => s!"({go a} >>> {go b})"
  | .op .asr [a, b] =>
    s!"(BitVec.sshiftRight {go a} {go b}.toNat)"
  | .op .neg [a] => s!"(- {go a})"
  | .slice e hi lo => s!"(BitVec.extractLsb' {lo} {hi - lo + 1} {go e})"
  | .concat args =>
    match args with
    | [] => "(0 : BitVec 0)"
    | [a] => go a
    | a :: rest =>
      let aStr := go a
      let restStr := go (Expr.concat rest)
      s!"({aStr} ++ {restStr})"
  | _ => s!"sorry /- unsupported expr: {repr expr} -/"

-- ============================================================================
-- Lean source generation
-- ============================================================================

/-- Generate complete Lean source file from a semantic model -/
def generateLean (model : SemanticModel) (extraWidths : List (String × Nat) := []) : String :=
  let ns := leanName model.moduleName
  let regWidths := model.registers.map fun r => (r.name, r.width)
  let inputWidths := model.inputs.map fun i => (i.name, i.width)
  -- Extra widths only for width inference, not for name resolution
  let allWidths := regWidths ++ inputWidths ++ extraWidths

  -- State structure
  let stateFields := model.registers.map fun r =>
    s!"  {leanName r.name} : BitVec {r.width}"
  let stateStruct := s!"structure State where\n" ++
    String.intercalate "\n" stateFields ++
    "\n  deriving DecidableEq, Repr, BEq, Inhabited\n"

  -- Input structure
  let inputFields := model.inputs.map fun i =>
    s!"  {leanName i.name} : BitVec {i.width}"
  let inputStruct := s!"structure Input where\n" ++
    String.intercalate "\n" inputFields ++
    "\n  deriving DecidableEq, Repr, BEq, Inhabited\n"

  -- nextState function — use register width to fix constant widths
  let regAssigns := model.registers.map fun r =>
    -- Gap O (P2D5): twin of Macro.lean nextState const-fix — generateLean
    -- string-codegen path. Same defect (reset predicate left at 0#32 vs
    -- BitVec 1 because fixConstWidths skips mux conditions), same fix; both
    -- sites patched in the same closure (compose-don't-replace).
    let fixedExpr :=
      fixConstWidthsSmart (fixConstWidths r.nextExpr r.width allWidths) allWidths
    s!"    {leanName r.name} := {irExprToLean fixedExpr regWidths inputWidths allWidths "s" "i"}"
  let nextStateFn := "def nextState (s : State) (i : Input) : State :=\n  {\n" ++
    String.intercalate "\n" regAssigns ++
    "\n  }\n"

  -- Initial state
  let initFields := model.registers.map fun r =>
    s!"    {leanName r.name} := ({r.initValue}#{ r.width})"
  let initState := "def initState : State :=\n  {\n" ++
    String.intercalate "\n" initFields ++
    "\n  }\n"

  -- Assemble
  s!"/-\n  Auto-generated semantic model from Verilog module: {model.moduleName}\n  Generated by Sparkle SVParser Verify\n-/\n\n" ++
  s!"namespace {ns}.Verify\n\n" ++
  stateStruct ++ "\n" ++
  inputStruct ++ "\n" ++
  nextStateFn ++ "\n" ++
  initState ++ "\n" ++
  s!"end {ns}.Verify\n"

-- ============================================================================
-- Combined pipeline: Module → Lean source
-- ============================================================================

/-- Extract model from IR Module and generate Lean verification source -/
def moduleToLean (m : Module) : String :=
  let model := extractModel m
  let regNames := model.registers.map (·.name)
  -- Exclude register assigns from wire inlining (registers are state, not wires)
  let assigns := (collectAssigns m.body).filter fun (n, _) => !regNames.any (· == n)
  -- Inline wire references in all register next-expressions
  let model := { model with
    registers := model.registers.map fun r =>
      { r with nextExpr := inlineAssigns assigns r.nextExpr }
  }
  -- Collect all wire widths for accurate width inference
  let wireWidths := m.wires.map fun w => (w.name, w.ty.bitWidth)
  let portWidths := m.inputs.map fun p => (p.name, p.ty.bitWidth)
  let allWidths := wireWidths ++ portWidths
  generateLean model allWidths

end Tools.SVParser.Verify
