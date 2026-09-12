import Witgen.U64.Export

namespace Witgen.U64.Tests
open Witgen.Typed Witgen.Methods Lean

/-- Reference inputs only. Composite / tiny moduli are deliberate generic-ring tests,
not invented curve parameters. Named field moduli come from Typed.modulus. -/
def testModuli : List Nat :=
  ([1,2,3,17,radix-1,radix,radix+1,2^128-1,2^192+1,2^255-19,capacity-1] ++
    [modulus bn254Fr,modulus secpBase,modulus secpScalar]).eraseDups

def casesFor (p : Nat) : List (Nat × Nat) :=
  let edges := [(0,0),(0,1),(1,0),(1,1),(p-1,p-1),(p-1,1),(p-2,p-3),
    (radix-1,1),(radix-1,radix-1),(radix+1,radix-1),
    (2^127+17,2^129+3),(2^192+7,2^193+11),(2^255-1,2^255-1),
    (2^255+1,p-1),(capacity-1,capacity-1)]
  let patterns := (List.range 16).map fun i =>
    (2^(16*i)+2^(255-i)+i*65537, 2^(255-16*i)+2^(64+i)+i*4294967291)
  let exhaustive := if p ≤ 17 then (List.range p).flatMap fun a => (List.range p).map (a,·) else []
  ((edges ++ patterns ++ exhaustive).map fun (a,b) => (a%p,b%p)).eraseDups

def require (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Checks algorithms and separately the actual generic stored method ASTs against
independent Nat addition/multiplication/modulo. No target output is normalized. -/
def checkPair (p a b : Nat) : IO Unit := do
  let wp := Word4.encode p
  let wa := Word4.encode a
  let wb := Word4.encode b
  let add := Word4.Add wp wa wb
  let mul := Word4.Mul wp wa wb
  let square := Word4.Square wp wa
  let bodyAdd := addBody.eval ((Library.nil : Library U64Op []).model primitive) h![wp,wa,wb]
  let bodyMul := mulBody.eval (addLibrary.model primitive) h![wp,wa,wb]
  let bodySquare := squareBody.eval (mulLibrary.model primitive) h![wp,wa]
  let context := s!"p={p}, a={a}, b={b}"
  require (add.decode == (a+b)%p && add.decode < p) ("Add/model: " ++ context)
  require (mul.decode == (a*b)%p && mul.decode < p) ("Mul/model: " ++ context)
  require (square.decode == (a*a)%p && square.decode < p) ("Square/model: " ++ context)
  require (decide (bodyAdd = add ∧ bodyMul = mul ∧ bodySquare = square)) ("AST/algorithm: " ++ context)

def fixture (f : FieldId) (op : String) (inputs : List Nat) (expected : Nat) (actual : Word4) : Json :=
  Json.mkObj [("program", .str ("field." ++ toString f.val ++ "." ++ op)),
    ("field", toJson f.val), ("modulus", .str (toString (modulus f))),
    ("inputs", toJson (inputs.map toString)), ("expected", .str (toString expected)),
    ("actual", .str (toString actual.decode)), ("limbs", wordJson actual)]

/-- Actual source FieldOp callers are lowered by the certified Handler and then
run through the single 12-method target library. -/
def checkFieldPair (f : FieldId) (a b : Nat) : IO (Array Json) := do
  let p := modulus f
  let fa := Residue.ofNat (modulus_pos f) a
  let fb := Residue.ofNat (modulus_pos f) b
  let wa := Word4.encode a
  let wb := Word4.encode b
  let sAdd := (sourceAdd f).eval anyFieldModel h![fa,fb]
  let sMul := (sourceMul f).eval anyFieldModel h![fa,fb]
  let sSquare := (sourceSquare f).eval anyFieldModel h![fa]
  let add := (compile (sourceAdd f) (by rfl)).eval (allLibrary.model primitive) h![wa,wb]
  let mul := (compile (sourceMul f) (by rfl)).eval (allLibrary.model primitive) h![wa,wb]
  let square := (compile (sourceSquare f) (by rfl)).eval (allLibrary.model primitive) h![wa]
  require (add.decode == (a+b)%p && add.decode == sAdd.val && add.decode < p) "field Add raw mismatch"
  require (mul.decode == (a*b)%p && mul.decode == sMul.val && mul.decode < p) "field Mul raw mismatch"
  require (square.decode == (a*a)%p && square.decode == sSquare.val && square.decode < p) "field Square raw mismatch"
  return #[fixture f "add" [a,b] ((a+b)%p) add, fixture f "mul" [a,b] ((a*b)%p) mul,
    fixture f "square" [a] ((a*a)%p) square]

def run : IO Json := do
  let mut pairs := 0
  let mut fieldPairs := 0
  let mut fixtures := #[]
  for p in testModuli do
    require (0 < p && p < capacity) "invalid test modulus"
    for (a,b) in casesFor p do
      checkPair p a b
      pairs := pairs + 1
  for f in [bn254Fr,secpBase,secpScalar] do
    for (a,b) in casesFor (modulus f) do
      fixtures := fixtures ++ (← checkFieldPair f a b)
      fieldPairs := fieldPairs + 1
  -- Decisive negative control: dropping sumCarry makes this addition wrong.
  let p := capacity-1
  let w := Word4.encode (p-1)
  let sum := Word4.addCarry w w
  let diff := Word4.subBorrow sum.1 (Word4.encode p)
  let broken := if !diff.2 then diff.1 else sum.1
  require (sum.2 && diff.2) "overflow+borrow boundary not exercised"
  require (broken.decode != ((p-1)+(p-1))%p) "missing-carry negative control did not fail"
  return Json.mkObj [("status", .str "pass"), ("moduli", toJson testModuli.length),
    ("generic_pairs", toJson pairs), ("generic_algorithm_checks", toJson (pairs*3)),
    ("generic_body_checks", toJson (pairs*3)), ("field_pairs", toJson fieldPairs),
    ("field_caller_checks", toJson fixtures.size), ("overflow_negative_control", .bool true),
    ("fixtures", .arr fixtures)]

end Witgen.U64.Tests
