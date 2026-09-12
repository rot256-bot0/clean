import Lean
import Witgen.Structs

/-! Named authoring elaborates directly to the existing intrinsically scoped AST.
There is no monadic function/closure node and no new core constructor. -/
namespace Witgen

structure Step {S : Type} (F : Signature S) (Γ : List S) (t : S) where
  args : List S
  shapes : List (RegionShape S)
  op : F args shapes t
  refs : HList (Var Γ) args
  regions : Regions F shapes

variable {S : Type} {F : Signature S} {V : S → Type} {Γ : List S} {s t : S}

def Step.bind (step : Step F Γ s) (next : Program F (s :: Γ) t) : Program F Γ t :=
  .let_ step.op step.refs step.regions next

def Step.bindNamed (step : Step F Γ s)
    (next : Var (s :: Γ) s → Program F (s :: Γ) t) : Program F Γ t :=
  step.bind (next .zero)

/-- Pure authoring lets deliberately support reference aliases only. -/
def referenceAlias (ref : Var Γ t) : Var Γ t := ref

def Var.weakenBy (_new : Var (s :: Γ) s) (old : Var Γ t) : Var (s :: Γ) t := .succ old

@[simp] theorem Step.eval_bind (M : Model F V) (step : Step F Γ s)
    (next : Program F (s :: Γ) t) (env : HList V Γ) :
    (step.bind next).eval M env = next.eval M
      (.cons (M.eval step.op (step.refs.map (fun r => r.get env)) (step.regions.eval M)) env) := rfl

def call {F G : Signature S} [Has G F] (op : G args shapes t)
    (refs : HList (Var Γ) args) (regions : Regions F shapes) : Step F Γ t :=
  ⟨args, shapes, Has.inject op, refs, regions⟩

def makeStruct {S Schema : Type} {F : Signature S} {Γ : List S}
    (desc : Schema → StructDesc S) [Has (StructOp desc) F]
    (schema : Schema) (args : HList (Var Γ) (desc schema).sorts) :
    Step F Γ (desc schema).result := call (.make schema : StructOp desc _ _ _) args .nil

def makeNamedStruct {S Schema : Type} {F : Signature S} {Γ : List S}
    (desc : Schema → StructDesc S) [Has (StructOp desc) F]
    (schema : Schema) (args : NamedArgs (Var Γ) (desc schema).fields) :
    Step F Γ (desc schema).result := makeStruct desc schema args.values

syntax "fields![" (ident " := " term),* "]" : term
open Lean in
macro_rules
  | `(fields![]) => `(NamedArgs.nil)
  | `(fields![$name:ident := $value]) =>
      `(NamedArgs.cons $(quote name.getId.toString) $value NamedArgs.nil)
  | `(fields![$name:ident := $value, $[$names:ident := $values],*]) =>
      `(NamedArgs.cons $(quote name.getId.toString) $value fields![$[$names:ident := $values],*])

def getField {S Schema : Type} {F : Signature S} {Γ : List S}
    (desc : Schema → StructDesc S) [Has (StructOp desc) F]
    (schema : Schema) (name : String) {t : S}
    [NamedField (desc schema).fields name t] (value : Var Γ (desc schema).result) :
    Step F Γ t := call (.get schema (name := name) NamedField.ref : StructOp desc _ _ _)
      (.cons value .nil) .nil

namespace struct

/-- Named functional construction through the generic structure feature. -/
def Named {S Schema : Type} {F : Signature S} {Γ : List S}
    (desc : Schema → StructDesc S) [Has (StructOp desc) F]
    (schema : Schema) (args : NamedArgs (Var Γ) (desc schema).fields) :
    Step F Γ (desc schema).result := makeNamedStruct desc schema args

def Get {S Schema : Type} {F : Signature S} {Γ : List S}
    (desc : Schema → StructDesc S) [Has (StructOp desc) F]
    (schema : Schema) (name : String) {t : S}
    [NamedField (desc schema).fields name t] (record : Var Γ (desc schema).result) :
    Step F Γ t := getField desc schema name record

/-- Return a new record value. No reference or source binding is modified. -/
def Set {S Schema : Type} {F : Signature S} {Γ : List S}
    (desc : Schema → StructDesc S) [Has (StructOp desc) F]
    (schema : Schema) (name : String) {t : S}
    [NamedField (desc schema).fields name t]
    (record : Var Γ (desc schema).result) (value : Var Γ t) :
    Step F Γ (desc schema).result :=
  call (.set schema (name := name) NamedField.ref : StructOp desc _ _ _)
    (.cons record (.cons value .nil)) .nil

end struct

syntax "h![" term,* "]" : term
macro_rules
  | `(h![]) => `(HList.nil)
  | `(h![$x]) => `(HList.cons $x HList.nil)
  | `(h![$x, $xs,*]) => `(HList.cons $x h![$xs,*])

syntax "regions![" term,* "]" : term
macro_rules
  | `(regions![]) => `(Regions.nil)
  | `(regions![$x]) => `(Regions.cons $x Regions.nil)
  | `(regions![$x, $xs,*]) => `(Regions.cons $x regions![$xs,*])

def inputRefs {S : Type} : (Γ : List S) → HList (Var Γ) Γ
  | [] => .nil
  | _ :: Γ => .cons .zero ((inputRefs Γ).map (fun r => .succ r))

def Program.withInputs (body : HList (Var Γ) Γ → Program F Γ t) : Program F Γ t :=
  body (inputRefs Γ)

open Lean Parser.Term in
private def expandNamed (names : List Ident) : List DoElem → MacroM Term
  | [] => Macro.throwError "witgen block must end in return"
  | elem :: rest => do
    match elem with
    | `(doElem| return $value) =>
      unless rest.isEmpty do Macro.throwErrorAt elem "return must end the witgen block"
      `(Program.ret $value)
    | `(doElem| let $name:ident ← $rhs:term) =>
      let kept := names.filter fun n => n.getId != name.getId
      let mut tail ← expandNamed (name :: kept) rest
      let fresh ← `(fresh)
      tail ← `(let $name := $fresh; $tail)
      for old in kept.reverse do
        tail ← `(let $old := Var.weakenBy $fresh $old; $tail)
      `(Step.bindNamed $rhs (fun fresh => $tail))
    | `(doElem| let $name:ident := $rhs:term) =>
      let tail ← expandNamed (name :: names.filter (fun n => n.getId != name.getId)) rest
      `(let $name := referenceAlias $rhs; $tail)
    | _ => Macro.throwErrorAt elem "witgen supports named let ←, reference-alias let :=, and return; use explicit closed regions for control"

open Lean Meta in
/-- Named blocks have a deliberately closed ambient interface, not a syntactic
reference denylist. Only scalar static data, type-valued families, and the checked
capability shape below are accepted. In particular, abstract values, arbitrary
functions, records, classes, and proofs are NOT presumed reference-free. -/
private def isClosedAmbientType (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if [``Nat, ``Int, ``Bool, ``String, ``Char, ``PUnit,
      ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize].any type.isConstOf then
    return true
  if type.isAppOfArity ``Fin 1 then
    return true
  if type.isAppOfArity ``Has 3 then
    -- Has is not a blanket "contains no references" certificate. Its only data
    -- result must stay opaque: a bare abstract destination signature parameter.
    -- A concrete/let-defined destination could instead return Var or a ref box.
    let target ← whnf type.getAppArgs[2]!
    if let .fvar id := target then
      return (← id.getDecl).value?.isNone
    return false
  -- These parameters produce types, not values of an unknown carrier. This
  -- admits S : Type and F : Signature S, but NOT x : S or f : Unit → S.
  forallTelescopeReducing type fun _ result => pure result.isSort

open Lean Meta in
/-- The only approved uses of ambient dictionaries are direct instance arguments
of fully applied, globally defined Step/Program builders. A Has dictionary is not
available for arbitrary host-language inspection or reference construction. The
global builders remain trusted authoring code, like all low-level AST helpers. -/
private def capabilityPositions (name : Name) (numArgs : Nat) : MetaM (Array Nat) := do
  forallTelescopeReducing (← getConstInfo name).type fun params result => do
    unless params.size == numArgs &&
        (result.isAppOfArity ``Step 4 || result.isAppOfArity ``Program 4) do
      return #[]
    let mut positions := #[]
    for i in [:params.size] do
      let decl ← params[i]!.fvarId!.getDecl
      if decl.binderInfo.isInstImplicit && (← whnf decl.type).isAppOfArity ``Has 3 then
        positions := positions.push i
    return positions

open Lean Meta in
/-- Free locals used as ordinary data, excluding only the checked capability
argument positions. No reduction of the user's term: beta/zeta reduction could
erase a forbidden dependency before it is checked. -/
private partial def collectAmbientData (used : FVarIdSet) (e : Expr) : MetaM FVarIdSet := do
  if !e.hasFVar then return used
  match e with
  | .fvar id => return used.insert id
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let positions ← match fn with
      | .const name _ => capabilityPositions name args.size
      | _ => pure #[]
    let mut used ← collectAmbientData used fn
    for i in [:args.size] do
      unless positions.contains i && args[i]!.isFVar do
        used ← collectAmbientData used args[i]!
    return used
  | .lam _ ty body _ | .forallE _ ty body _ =>
    collectAmbientData (← collectAmbientData used ty) body
  | .letE _ ty value body _ =>
    collectAmbientData (← collectAmbientData (← collectAmbientData used ty) value) body
  | .mdata _ body | .proj _ _ body => collectAmbientData used body
  | _ => return used

/-- Reject ambient locals outside the closed interface, even at an identically
indexed context. Follow dependencies in both types and let values: accepting a
Nat alias must not launder an outer reference used to compute that Nat. This is
an authoring check, not a provenance theorem or part of the proof kernel. -/
syntax (name := closedNamed) "closed_witgen% " term : term

open Lean Meta Elab Term in
@[term_elab closedNamed] def elabClosedNamed : TermElab := fun stx expectedType => do
  let outer ← getLCtx
  let expression ← elabTerm stx[1] expectedType
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasExprMVar then
    throwErrorAt stx "unresolved witgen term; solve holes before entering the closed block"
  let mut used := collectFVars {} expression
  let mut dataUsed ← collectAmbientData {} expression
  let declarations := outer.foldl (fun acc decl => acc.push decl) (#[] : Array LocalDecl)
  for decl in declarations.reverse do
    if used.fvarSet.contains decl.fvarId then
      let type ← instantiateMVars decl.type
      let value? ← decl.value?.mapM instantiateMVars
      if type.hasExprMVar || value?.any Expr.hasExprMVar then
        throwErrorAt stx "unresolved witgen dependency '{decl.userName}'; solve holes before entering the closed block"
      let ty ← whnf type
      unless (← isClosedAmbientType ty) &&
          (!ty.isAppOfArity ``Has 3 || !dataUsed.contains decl.fvarId) do
        throwErrorAt stx "implicit witgen capture '{decl.userName}'; declare it as a region input and pass it explicitly"
      used := collectFVars used type
      dataUsed ← collectAmbientData dataUsed type
      if let some value := value? then
        used := collectFVars used value
        dataUsed ← collectAmbientData dataUsed value
  return expression

open Lean Parser.Term in
macro "witgen" "[" names:ident,* "]" "do" body:doSeq : term => do
  let ns := names.getElems.toList
  if (ns.map (·.getId)).eraseDups.length != ns.length then
    Macro.throwError "duplicate witgen input name"
  let out ← expandNamed ns (getDoElems body).toList
  let args : Array Term := ns.toArray.map fun n => ⟨n.raw⟩
  `(closed_witgen% (Program.withInputs (fun | h![$args,*] => $out)))

end Witgen
