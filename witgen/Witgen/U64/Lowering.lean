import Witgen.U64.FieldTarget

namespace Witgen.U64
open Witgen.Typed Witgen.Methods

/-- Exact raw-representative relation; it does not normalize target outputs.
Product/option sorts retain their structural meaning for composition. -/
def Rep : (t : Ty) → FieldVal t → Val t → Prop
  | .field _, a, w => w.decode = a.val
  | .nat, a, b => a = b
  | .bool, a, b => a = b
  | .u64, a, b => a = b
  | .word4, a, w => a = (w.l0,w.l1,w.l2,w.l3)
  | .point, a, b => a = b
  | .pair a b, x, y => Rep a x.1 y.1 ∧ Rep b x.2 y.2
  | .option a, some x, some y => Rep a x y
  | .option _, none, none => True
  | .option _, _, _ => False

theorem canonical_of_rep {f : FieldId} (a : FieldValue f) (w : Word4)
    (h : w.decode = a.val) : Word4.Canonical (wordModulus f).decode w := by
  rw [Word4.Canonical, wordModulus_decode, h]
  exact a.isLt

theorem fieldAdd_spec (f : FieldId) (a b : FieldValue f) (aw bw : Word4)
    (ha : aw.decode = a.val) (hb : bw.decode = b.val) :
    ((allLibrary.model primitive).eval (.inr (.call (fieldAddRef f))) h![aw,bw] .nil).decode =
      (Residue.add a b).val := by
  rw [fieldAdd_eval]
  have hp : 0 < (wordModulus f).decode := by rw [wordModulus_decode]; exact modulus_pos f
  have h := Word4.Add_correct (wordModulus f) aw bw hp
    (canonical_of_rep a aw ha) (canonical_of_rep b bw hb)
  simpa only [wordModulus_decode, ha, hb, Residue.add, Residue.ofNat] using h.1

theorem fieldMul_spec (f : FieldId) (a b : FieldValue f) (aw bw : Word4)
    (ha : aw.decode = a.val) (hb : bw.decode = b.val) :
    ((allLibrary.model primitive).eval (.inr (.call (fieldMulRef f))) h![aw,bw] .nil).decode =
      (Residue.mul a b).val := by
  rw [fieldMul_eval]
  have hp : 0 < (wordModulus f).decode := by rw [wordModulus_decode]; exact modulus_pos f
  have h := Word4.Mul_correct (wordModulus f) aw bw hp
    (canonical_of_rep a aw ha) (canonical_of_rep b bw hb)
  simpa only [wordModulus_decode, ha, hb, Residue.mul, Residue.ofNat] using h.1

theorem fieldSquare_spec (f : FieldId) (a : FieldValue f) (aw : Word4)
    (ha : aw.decode = a.val) :
    ((allLibrary.model primitive).eval (.inr (.call (fieldSquareRef f))) h![aw] .nil).decode =
      (Residue.square a).val := by
  rw [fieldSquare_eval]
  have hp : 0 < (wordModulus f).decode := by rw [wordModulus_decode]; exact modulus_pos f
  have h := Word4.Square_correct (wordModulus f) aw hp (canonical_of_rep a aw ha)
  simpa only [wordModulus_decode, ha, Residue.square, Residue.ofNat,
    Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul] using h.1

/-- Each arithmetic caller operation becomes exactly one shared call ref.
Literal normalization happens while constructing the target AST, not at runtime. -/
def lower : Handler AnyFieldOp (WithCalls U64Op allSigs) :=
  fun (.field f op) => match op with
    | .const n => .inl (.fieldLiteral f (Word4.encode (n % modulus f)))
    | .add => .inr (.call (fieldAddRef f))
    | .mul => .inr (.call (fieldMulRef f))
    | .square => .inr (.call (fieldSquareRef f))

theorem lower_respects : anyFieldModel.Respects (allLibrary.model primitive) lower Rep := by
  intro args shapes t op xs ys fs gs hr _
  cases op with
  | field f op =>
    cases op with
    | const n =>
      cases xs; cases ys; cases fs; cases gs
      change (Word4.encode (n % modulus f)).decode = n % modulus f
      exact Word4.decode_encode_of_lt (Nat.lt_trans (Nat.mod_lt _ (modulus_pos f)) (modulus_lt f))
    | add =>
      cases xs with | cons a xs =>
        cases xs with | cons b xs =>
          cases xs
          cases ys with | cons aw ys =>
            cases ys with | cons bw ys =>
              cases ys; cases fs; cases gs
              exact fieldAdd_spec f a b aw bw hr.1 hr.2.1
    | mul =>
      cases xs with | cons a xs =>
        cases xs with | cons b xs =>
          cases xs
          cases ys with | cons aw ys =>
            cases ys with | cons bw ys =>
              cases ys; cases fs; cases gs
              exact fieldMul_spec f a b aw bw hr.1 hr.2.1
    | square =>
      cases xs with | cons a xs =>
        cases xs
        cases ys with | cons aw ys =>
          cases ys; cases fs; cases gs
          exact fieldSquare_spec f a aw hr.1

/-- Discharged, reusable implementation certificate over actual registered bodies. -/
def certified : CertifiedLowering anyFieldModel (allLibrary.model primitive) Rep :=
  .ofHandler _ _ lower Rep lower_respects

/-- No unrolling/proof replay at source call sites: one generic core induction. -/
theorem caller_correct (p : Program AnyFieldOp Γ t) (xs : HList FieldVal Γ)
    (ys : HList Val Γ) (h : HList.Rel Rep xs ys) :
    Rep t (p.eval anyFieldModel xs) ((p.mapHandler lower).eval (allLibrary.model primitive) ys) :=
  Program.eval_mapHandler_related lower anyFieldModel (allLibrary.model primitive) Rep lower_respects p xs ys h

end Witgen.U64
