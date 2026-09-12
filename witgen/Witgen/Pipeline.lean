import Witgen.Demo

namespace Witgen.Demo
open Arithmetic

/-- All formal argument references, in the exact declared order. -/
def refs {S : Type} : (Γ : List S) → HList (Var Γ) Γ
  | [] => .nil
  | _ :: Γ => .cons .zero ((refs Γ).map (fun r => .succ r))

theorem map_map {S : Type} {V W U : S → Type}
    {Γ : List S} (f : {s : S} → V s → W s) (g : {s : S} → W s → U s) (xs : HList V Γ) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [HList.map, ih]

theorem refs_eval {S : Type} {Γ : List S} {V : S → Type} (xs : HList V Γ) :
    (refs Γ).map (fun r => r.get xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [refs, HList.map, map_map, Var.get, ih]

def emit (op : F args shapes t) (regions : Regions F shapes) : Program F args t :=
  .let_ op (refs args) regions (.ret .zero)

theorem emit_eval (M : Model F V) (op : F args shapes t)
    (regions : Regions F shapes) (xs : HList V args) :
    (emit op regions).eval M xs = M.eval op xs (regions.eval M) := by
  simp only [emit, Program.eval, refs_eval, Var.get]

/-- Representation changes lift structurally to all optional aggregate sorts. -/
def Graph (f : α → β) (t : Ty) (x : Val α t) (y : Val β t) : Prop :=
  Val.map f x = y

theorem graph_env (f : α → β) (xs : HList (Val α) Γ) :
    HList.Rel (Graph f) xs (xs.map (Val.map f)) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem graph_env_eq (f : α → β) (xs : HList (Val α) Γ) (ys : HList (Val β) Γ)
    (h : HList.Rel (Graph f) xs ys) : xs.map (Val.map f) = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have hx : Val.map f x = y := h.1
      simp only [HList.map, hx, ih ys h.2]

theorem data_respects (f : α → β) :
    (dataModel α).Respects (dataModel β) (Handler.id DataOp) (Graph f) := by
  intro args shapes t op xs ys fs gs hr _
  rw [← graph_env_eq f xs ys hr]
  clear hr ys
  cases op <;> cases xs
  all_goals try (rename_i a xs; cases xs)
  all_goals try (rename_i b xs; cases xs)
  all_goals try (rename_i c xs; cases xs)
  all_goals simp [Graph, Handler.id, dataModel, HList.map, Val.map, List.map_append]

theorem control_respects (f : α → β) :
    (controlModel α).Respects (controlModel β) (Handler.id Control) (Graph f) := by
  intro args shapes t op xs ys fs gs hr hb
  rw [← graph_env_eq f xs ys hr]
  clear hr ys
  cases op with
  | branch captures result =>
    cases xs with
    | cons b caps =>
      cases fs with
      | cons yes fs =>
        cases fs with
        | cons no fs =>
          cases fs
          cases gs with
          | cons yes' gs =>
            cases gs with
            | cons no' gs =>
              cases gs
              cases b
              · exact hb.2.1 caps _ (graph_env f caps)
              · exact hb.1 caps _ (graph_env f caps)
  | map captures input output =>
    cases xs with
    | cons xs caps =>
      cases fs with
      | cons body fs =>
        cases fs
        cases gs with
        | cons body' gs =>
          cases gs
          change List.map (Val.map f) (List.map (fun x => body (.cons x caps)) xs) =
            List.map (fun x => body' (.cons x (caps.map (Val.map f)))) (List.map (Val.map f) xs)
          simp only [List.map_map]
          apply List.map_congr_left
          intro x _
          exact hb.1 (.cons x caps) _ (graph_env f (.cons x caps))
  | fold captures element accumulator =>
    cases xs with
    | cons xs rest =>
      cases rest with
      | cons initial caps =>
        cases fs with
        | cons body fs =>
          cases fs
          cases gs with
          | cons body' gs =>
            cases gs
            change Val.map f (xs.foldl (fun acc x => body (.cons x (.cons acc caps))) initial) =
              (List.map (Val.map f) xs).foldl
                (fun acc x => body' (.cons x (.cons acc (caps.map (Val.map f))))) (Val.map f initial)
            induction xs generalizing initial with
            | nil => rfl
            | cons x xs ih =>
              simp only [List.foldl_cons, List.map_cons]
              have step := hb.1 (.cons x (.cons initial caps)) _
                (graph_env f (.cons x (.cons initial caps)))
              change Val.map f (body (.cons x (.cons initial caps))) =
                body' (.cons (Val.map f x) (.cons (Val.map f initial) (caps.map (Val.map f)))) at step
              rw [← step]
              exact ih _

theorem shared_respects (f : α → β) :
    ((dataModel α).sum (controlModel α)).Respects
      ((dataModel β).sum (controlModel β)) (Handler.id _) (Graph f) := by
  intro args shapes t op xs ys fs gs hr hb
  cases op with
  | inl op => exact data_respects f op xs ys fs gs hr hb
  | inr op => exact control_respects f op xs ys fs gs hr hb

/-- Field arithmetic expands to primitive integer arithmetic and an explicit reduction. -/
def fieldScalarToNat : Template FieldOp NatSig
  | _, _, _, .const n, _ => emit (.inl (.const (n % 17))) .nil
  | _, _, _, .add, _ =>
      .let_ (.inl .add) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const 17)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil <| .ret .zero
  | _, _, _, .mul, _ =>
      .let_ (.inl .mul) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const 17)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil <| .ret .zero
  | _, _, _, .eq, _ => emit (.inl .eq) .nil

def fieldToNat : Template FieldSig NatSig
  | _, _, _, .inl op, regions => fieldScalarToNat op regions
  | _, _, _, .inr op, regions => emit (.inr op) regions

/-- Syntax only: no preservation assertion for arbitrary unbounded Nat programs. -/
def natScalarToWord : Handler NatOp WordOp
  | _, _, _, .const n => .const n
  | _, _, _, .add => .add
  | _, _, _, .mul => .mul
  | _, _, _, .div => .div
  | _, _, _, .mod => .mod
  | _, _, _, .eq => .eq

def natToWord : Handler NatSig WordSig
  | _, _, _, .inl op => .inl (natScalarToWord op)
  | _, _, _, .inr op => .inr op

def fieldScalarToWord : Template FieldOp WordSig
  | _, _, _, .const n, _ => emit (.inl (.const (n % 17))) .nil
  | _, _, _, .add, _ =>
      .let_ (.inl .add) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const 17)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil <| .ret .zero
  | _, _, _, .mul, _ =>
      .let_ (.inl .mul) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const 17)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil <| .ret .zero
  | _, _, _, .eq, _ => emit (.inl .eq) .nil

def fieldToWord : Template FieldSig WordSig
  | _, _, _, .inl op, regions => fieldScalarToWord op regions
  | _, _, _, .inr op, regions => emit (.inr op) regions

def fieldWord (x : Field17) : UInt64 := UInt64.ofNat x.toNat

theorem fieldWord_toNat (x : Field17) : (fieldWord x).toNat = x.toNat :=
  u64_ofNat_toNat (lt_small_modulus_fits (n := 17) (by decide) x.isLt)

theorem fieldWord_injective : Function.Injective fieldWord := by
  intro x y h
  apply Fin.ext
  exact (fieldWord_toNat x).symm.trans ((congrArg UInt64.toNat h).trans (fieldWord_toNat y))

theorem fieldToNat_law :
    Template.Respects fieldModel natModel fieldToNat (Graph Field17.toNat) := by
  intro args shapes t op xs ys fs regions hr hb
  cases op with
  | inr op =>
    simp only [fieldToNat, emit_eval]
    exact shared_respects Field17.toNat op xs ys fs (regions.eval natModel) hr hb
  | inl op =>
    rw [← graph_env_eq Field17.toNat xs ys hr]
    cases op with
    | const n => cases xs; rfl
    | add => cases xs with
      | cons a xs => cases xs with
        | cons b xs => cases xs; rfl
    | mul => cases xs with
      | cons a xs => cases xs with
        | cons b xs => cases xs; rfl
    | eq => cases xs with
      | cons a xs => cases xs with
        | cons b xs =>
          cases xs
          change decide (a = b) = decide (a.val = b.val)
          simp only [Fin.ext_iff]

theorem fieldToWord_law :
    Template.Respects fieldModel wordModel fieldToWord (Graph fieldWord) := by
  intro args shapes t op xs ys fs regions hr hb
  cases op with
  | inr op =>
    simp only [fieldToWord, emit_eval]
    exact shared_respects fieldWord op xs ys fs (regions.eval wordModel) hr hb
  | inl op =>
    rw [← graph_env_eq fieldWord xs ys hr]
    cases op with
    | const n => cases xs; rfl
    | add =>
      cases xs with
      | cons a xs => cases xs with
        | cons b xs =>
          cases xs
          change fieldWord (Field17.add a b) = (fieldWord a + fieldWord b) % UInt64.ofNat 17
          apply UInt64.toNat_inj.mp
          exact (fieldWord_toNat _).trans (Field17.add_u64 a b).symm
    | mul =>
      cases xs with
      | cons a xs => cases xs with
        | cons b xs =>
          cases xs
          change fieldWord (Field17.mul a b) = (fieldWord a * fieldWord b) % UInt64.ofNat 17
          apply UInt64.toNat_inj.mp
          exact (fieldWord_toNat _).trans (Field17.mul_u64 a b).symm
    | eq =>
      cases xs with
      | cons a xs => cases xs with
        | cons b xs =>
          cases xs
          change decide (a = b) = decide (fieldWord a = fieldWord b)
          simp only [fieldWord_injective.eq_iff]

/-- Uniform endpoints cover nested control and complete aggregate returns. -/
theorem fieldToNat_correct (p : Program FieldSig Γ t) (xs : HList (Val Field17) Γ) :
    Val.map Field17.toNat (p.eval fieldModel xs) =
      (p.lower fieldToNat).eval natModel (xs.map (Val.map Field17.toNat)) :=
  Program.eval_lower_related _ _ _ _ fieldToNat_law p _ _ (graph_env _ xs)

theorem fieldToWord_correct (p : Program FieldSig Γ t) (xs : HList (Val Field17) Γ) :
    Val.map fieldWord (p.eval fieldModel xs) =
      (p.lower fieldToWord).eval wordModel (xs.map (Val.map fieldWord)) :=
  Program.eval_lower_related _ _ _ _ fieldToWord_law p _ _ (graph_env _ xs)

/-- Handler relabeling commutes with reference substitution and syntactic bind. -/
theorem mapHandler_subst {S : Type} {F G : Signature S}
    {Γ Δ : List S} {t : S}
    (h : Handler F G) (p : Program F Γ t) (σ : RefSubst Γ Δ) :
    (p.subst σ).mapHandler h = (p.mapHandler h).subst σ := by
  cases p with
  | ret r => rfl
  | let_ op args regions next =>
    simp only [Program.subst, Program.mapHandler, mapHandler_subst h next]

theorem mapHandler_bind {S : Type} {F G : Signature S}
    {Γ : List S} {s t : S}
    (h : Handler F G) (p : Program F Γ s) (next : Program F (s :: Γ) t) :
    (p.bind next).mapHandler h = (p.mapHandler h).bind (next.mapHandler h) := by
  cases p with
  | ret r => exact mapHandler_subst h next _
  | let_ op args regions tail =>
    simp only [Program.bind, Program.mapHandler, mapHandler_bind h tail, mapHandler_subst]

mutual
  theorem lower_natural {S : Type} {F G K : Signature S}
      {Γ : List S} {t : S}
      (T : Template F G) (U : Template F K) (h : Handler G K)
      (law : ∀ {args shapes t} (op : F args shapes t) regions,
        (T op regions).mapHandler h = U op (regions.mapHandler h))
      (p : Program F Γ t) : (p.lower T).mapHandler h = p.lower U := by
    match p with
    | .ret _ => rfl
    | .let_ op args regions next =>
      have hn := lower_natural T U h law next
      have hr := regions_lower_natural T U h law regions
      simp only [Program.lower, mapHandler_bind, mapHandler_subst, law, hr, hn]
  termination_by structural p
  theorem regions_lower_natural {S : Type} {F G K : Signature S}
      {shapes : List (RegionShape S)}
      (T : Template F G) (U : Template F K) (h : Handler G K)
      (law : ∀ {args shapes t} (op : F args shapes t) regions,
        (T op regions).mapHandler h = U op (regions.mapHandler h))
      (regions : Regions F shapes) : (regions.lower T).mapHandler h = regions.lower U := by
    match regions with
    | .nil => rfl
    | .cons body rest =>
      have hb := lower_natural T U h law body
      have hr := regions_lower_natural T U h law rest
      simp only [Regions.lower, Regions.mapHandler, hb, hr]
  termination_by structural regions
end

theorem fieldTemplate_commutes (op : FieldSig args shapes t) (regions : Regions NatSig shapes) :
    (fieldToNat op regions).mapHandler natToWord =
      fieldToWord op (regions.mapHandler natToWord) := by
  cases op with
  | inr op => rfl
  | inl op => cases op <;> rfl

/-- Equality of actual syntax, including every nested region and continuation. -/
theorem lower_commutes (p : Program FieldSig Γ t) :
    (p.lower fieldToNat).mapHandler natToWord = p.lower fieldToWord :=
  lower_natural _ _ _ fieldTemplate_commutes p

theorem Val.map_comp (f : α → β) (g : β → γ) (t : Ty) (x : Val α t) :
    Val.map g (Val.map f x) = Val.map (fun a => g (f a)) x := by
  induction t with
  | scalar => rfl
  | bool => rfl
  | quad => rfl
  | modmul => rfl
  | list t ih =>
    simp only [Val.map, List.map_map]
    apply List.map_congr_left
    intro a _
    exact ih a

theorem Val.fieldWord_roundtrip (t : Ty) (x : Val Field17 t) :
    Val.map UInt64.toNat (Val.map fieldWord x) = Val.map Field17.toNat x := by
  rw [Val.map_comp]
  have h : (fun x => (fieldWord x).toNat) = Field17.toNat := funext fieldWord_toNat
  rw [h]

/-- Applicability endpoint restricted to the image of the proved Field17 lowering.
No theorem asserts that arbitrary unbounded Nat operations fit into a word. -/
theorem natToWord_fieldImage_correct (p : Program FieldSig Γ t)
    (xs : HList (Val Field17) Γ) :
    Val.map UInt64.toNat (((p.lower fieldToNat).mapHandler natToWord).eval wordModel
      (xs.map (Val.map fieldWord))) =
      (p.lower fieldToNat).eval natModel (xs.map (Val.map Field17.toNat)) := by
  rw [lower_commutes, ← fieldToWord_correct, Val.fieldWord_roundtrip, fieldToNat_correct]

def quadraticNat : Program NatSig [.scalar, .scalar] .quad :=
  quadraticField.lower fieldToNat

def quadraticWord : Program WordSig [.scalar, .scalar] .quad :=
  quadraticNat.mapHandler natToWord

theorem quadraticNat_correct (x c : Field17) :
    quadraticNat.eval natModel (.cons x.toNat (.cons c.toNat .nil)) =
      (⟨(Field17.mul x x).toNat, (Field17.add (Field17.mul x x) c).toNat⟩ : Quad Nat) :=
  (fieldToNat_correct quadraticField (.cons x (.cons c .nil))).symm

theorem quadraticWord_eval (x c : Field17) :
    quadraticWord.eval wordModel (.cons (fieldWord x) (.cons (fieldWord c) .nil)) =
      (⟨fieldWord (Field17.mul x x), fieldWord (Field17.add (Field17.mul x x) c)⟩ : Quad UInt64) := by
  change ((quadraticField.lower fieldToNat).mapHandler natToWord).eval wordModel _ = _
  rw [lower_commutes]
  exact (fieldToWord_correct quadraticField (.cons x (.cons c .nil))).symm

theorem quadraticWord_correct (x c : Field17) :
    Val.map UInt64.toNat (t := .quad)
      (quadraticWord.eval wordModel (.cons (fieldWord x) (.cons (fieldWord c) .nil))) =
      (⟨(Field17.mul x x).toNat, (Field17.add (Field17.mul x x) c).toNat⟩ : Quad Nat) := by
  rw [quadraticWord_eval]
  simp only [Val.map, fieldWord_toNat]

def modMulWord : Program WordSig [.scalar, .scalar, .scalar] .modmul :=
  modMulNat.mapHandler natToWord

theorem modMulWord_eval (a b n : UInt64) :
    modMulWord.eval wordModel (.cons a (.cons b (.cons n .nil))) =
      (⟨a * b, a * b / n, a * b % n⟩ : ModMul UInt64) := rfl

/-- Complete-record correspondence of the actual transformed program. -/
theorem modMulWord_correct {a b n : Nat}
    (ha : FitsU64 a) (hb : FitsU64 b) (hn : FitsU64 n)
    (hp : FitsU64 (a * b)) (hpos : 0 < n) :
    Val.map UInt64.toNat (t := .modmul)
      (modMulWord.eval wordModel
        (.cons (UInt64.ofNat a) (.cons (UInt64.ofNat b) (.cons (UInt64.ofNat n) .nil)))) =
      modMulNat.eval natModel (.cons a (.cons b (.cons n .nil))) :=
  congrArg (fun w : MulModWitness => (⟨w.product, w.quotient, w.remainder⟩ : ModMul Nat))
    (genMulModU64_correct ha hb hn hp hpos)

theorem modMulWord_small_correct {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    Val.map UInt64.toNat (t := .modmul)
      (modMulWord.eval wordModel
        (.cons (UInt64.ofNat a) (.cons (UInt64.ofNat b) (.cons (UInt64.ofNat n) .nil)))) =
      modMulNat.eval natModel (.cons a (.cons b (.cons n .nil))) :=
  modMulWord_correct (lt_small_modulus_fits hn ha) (lt_small_modulus_fits hn hb)
    (small_modulus_fits hn) (mul_fits_of_small_modulus hn ha hb) hn.1

theorem modMulWord_small_satisfies {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    MulModRel a b n (ModMul.toArithmetic (Val.map UInt64.toNat (t := .modmul)
      (modMulWord.eval wordModel
        (.cons (UInt64.ofNat a) (.cons (UInt64.ofNat b) (.cons (UInt64.ofNat n) .nil)))))) := by
  rw [modMulWord_small_correct hn ha hb]
  exact modMulNat_satisfies a b n hn.1

/-! Generic optional map elimination. The base feature and its model are arbitrary;
input/output/capture sorts may themselves be records or nested lists. -/
abbrev Library (F : Signature Ty) := SigSum F (SigSum DataOp Control)

def libraryModel (M : Model F (Val α)) : Model (Library F) (Val α) :=
  M.sum ((dataModel α).sum (controlModel α))

def mapBodyToFold {F : Signature Ty} {captures : List Ty} {input output : Ty}
    (body : Program (Library F) (input :: captures) output) :
    Program (Library F) (input :: .list output :: captures) (.list output) :=
  (body.subst (RefSubst.lift (fun r => .succ r))).bind <|
    .let_ (.inr (.inl (.push output)))
      (.cons (.succ (.succ .zero)) (.cons .zero .nil)) .nil (.ret .zero)

def mapBlock {F : Signature Ty} {captures : List Ty} {input output : Ty}
    (body : Program (Library F) (input :: captures) output) :
    Program (Library F) (.list input :: captures) (.list output) :=
  .let_ (.inr (.inl (.empty output))) .nil .nil <|
  .let_ (.inr (.inr (.fold captures input (.list output))))
    (.cons (.succ .zero) (.cons .zero
      ((refs captures).map (fun r => .succ (.succ r)))))
    (.cons (mapBodyToFold body) .nil) (.ret .zero)

def mapToFold (F : Signature Ty) : Template (Library F) (Library F)
  | _, _, _, .inl op, regions => emit (.inl op) regions
  | _, _, _, .inr (.inl op), regions => emit (.inr (.inl op)) regions
  | _, _, _, .inr (.inr (.branch caps t)), regions => emit (.inr (.inr (.branch caps t))) regions
  | _, _, _, .inr (.inr (.fold caps a b)), regions => emit (.inr (.inr (.fold caps a b))) regions
  | _, _, _, .inr (.inr (.map _ _ _)), .cons body .nil => mapBlock body

theorem mapBodyToFold_eval {F : Signature Ty} {captures : List Ty} {input output : Ty}
    (M : Model F (Val α)) (body : Program (Library F) (input :: captures) output)
    (x : Val α input) (acc : List (Val α output)) (caps : HList (Val α) captures) :
    (mapBodyToFold body).eval (libraryModel M) (.cons x (.cons acc caps)) =
      acc ++ [body.eval (libraryModel M) (.cons x caps)] := by
  rw [mapBodyToFold, Program.eval_bind]
  change acc ++ [(body.subst
    (RefSubst.lift (t := input) (Δ := .list output :: captures) (fun r => .succ r))).eval
    (libraryModel M) (.cons x (.cons acc caps))] = _
  rw [Program.eval_subst (libraryModel M) body
    (RefSubst.lift (t := input) (Δ := .list output :: captures) (fun r => .succ r))
    (.cons x caps) (.cons x (.cons acc caps)) (by intro t r; cases r <;> rfl)]

theorem fold_push_map (f : α → β) (xs : List α) (acc : List β) :
    xs.foldl (fun acc x => acc ++ [f x]) acc = acc ++ xs.map f := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.map_nil, List.append_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, ih, List.append_assoc, List.singleton_append]

theorem mapBlock_eval {F : Signature Ty} {captures : List Ty} {input output : Ty}
    (M : Model F (Val α)) (body : Program (Library F) (input :: captures) output)
    (xs : List (Val α input)) (caps : HList (Val α) captures) :
    (mapBlock body).eval (libraryModel M) (.cons xs caps) =
      xs.map (fun x => body.eval (libraryModel M) (.cons x caps)) := by
  simp only [mapBlock, Program.eval, HList.map, map_map, Var.get, refs_eval, Regions.eval]
  change xs.foldl (fun acc x => (mapBodyToFold body).eval (libraryModel M)
    (.cons x (.cons acc caps))) [] = _
  simp only [mapBodyToFold_eval, fold_push_map, List.nil_append]

theorem eq_env {S : Type} {V : S → Type} {Γ : List S} (xs : HList V Γ) :
    HList.Rel (fun _ x y => x = y) xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem eq_of_env_rel {S : Type} {V : S → Type} {Γ : List S}
    (xs ys : HList V Γ) (h : HList.Rel (fun _ x y => x = y) xs ys) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys => simp only [h.1, ih ys h.2]

theorem eq_of_body_rel {S : Type} {V : S → Type} {shapes : List (RegionShape S)}
    (fs gs : HList (Body V) shapes) (h : HList.Rel (BodyRel (fun _ x y => x = y)) fs gs) :
    fs = gs := by
  induction fs with
  | nil => cases gs; rfl
  | cons f fs ih =>
    cases gs with
    | cons g gs =>
      have hfg : f = g := funext (fun xs => h.1 xs xs (eq_env xs))
      simp only [hfg, ih gs h.2]

theorem mapToFold_law {F : Signature Ty} (M : Model F (Val α)) :
    Template.Respects (libraryModel M) (libraryModel M) (mapToFold F) (fun _ x y => x = y) := by
  intro args shapes t op xs ys fs regions hr hb
  have hxy := eq_of_env_rel xs ys hr
  subst ys
  have hfg := eq_of_body_rel fs (regions.eval (libraryModel M)) hb
  subst fs
  cases op with
  | inl op => exact (emit_eval _ _ _ _).symm
  | inr op => cases op with
    | inl op => exact (emit_eval _ _ _ _).symm
    | inr op => cases op with
      | branch caps t => exact (emit_eval _ _ _ _).symm
      | fold caps a b => exact (emit_eval _ _ _ _).symm
      | map caps a b =>
        cases regions with
        | cons body rest =>
          cases rest
          cases xs with
          | cons xs caps => exact (mapBlock_eval M body xs caps).symm

/-- Uniform whole-program preservation using the kernel's macro lifting theorem. -/
theorem mapToFold_correct {F : Signature Ty} (M : Model F (Val α))
    (p : Program (Library F) Γ t) (xs : HList (Val α) Γ) :
    (p.lower (mapToFold F)).eval (libraryModel M) xs = p.eval (libraryModel M) xs :=
  (Program.eval_lower_related _ _ _ _ (mapToFold_law M) p xs xs (eq_env xs)).symm

def batchQuadraticFoldField := batchQuadraticField.lower (mapToFold FieldOp)
def batchQuadraticNat := batchQuadraticField.lower fieldToNat
def batchQuadraticWord := batchQuadraticNat.mapHandler natToWord

def conditionalBatchNat := conditionalBatchField.lower fieldToNat
def conditionalBatchWord := conditionalBatchNat.mapHandler natToWord
def conditionalBatchFoldField := conditionalBatchField.lower (mapToFold FieldOp)
def conditionalBatchFoldNat := conditionalBatchFoldField.lower fieldToNat
def conditionalBatchFoldWord := conditionalBatchFoldNat.mapHandler natToWord

theorem conditionalBatchFoldWord_correct (b : Bool) (xs : List Field17) (c : Field17) :
    Val.map UInt64.toNat (t := .list .quad)
      (conditionalBatchFoldWord.eval wordModel
        (.cons b (.cons (xs.map fieldWord) (.cons (fieldWord c) .nil)))) =
      Val.map Field17.toNat (t := .list .quad)
        (if b then xs.map (fun x => (⟨Field17.mul x x, Field17.add (Field17.mul x x) c⟩ : Quad Field17))
         else []) := by
  change Val.map UInt64.toNat (((conditionalBatchFoldField.lower fieldToNat).mapHandler natToWord).eval
    wordModel ((HList.cons b (.cons xs (.cons c .nil)) :
      HList (Val Field17) [.bool, .list .scalar, .scalar]).map (Val.map fieldWord))) = _
  rw [lower_commutes, ← fieldToWord_correct, Val.fieldWord_roundtrip]
  rw [show conditionalBatchFoldField = conditionalBatchField.lower (mapToFold FieldOp) from rfl]
  have hp : (conditionalBatchField.lower (mapToFold FieldOp)).eval fieldModel
      (.cons b (.cons xs (.cons c .nil))) =
      conditionalBatchField.eval fieldModel (.cons b (.cons xs (.cons c .nil))) :=
    mapToFold_correct fieldScalarModel conditionalBatchField _
  rw [hp, conditionalBatch_eval]

/-- The integer macro program is total even outside the word applicability domain. -/
theorem quadraticNat_eval (x c : Nat) :
    quadraticNat.eval natModel (.cons x (.cons c .nil)) =
      (⟨x * x % 17, (x * x % 17 + c) % 17⟩ : Quad Nat) := rfl

/-- Convenient Nat-facing bounded endpoint for downstream circuit encoders. -/
theorem quadraticWord_bounded (x c : Nat) (hx : x < 17) (hc : c < 17) :
    Val.map UInt64.toNat (t := .quad)
      (quadraticWord.eval wordModel (.cons (UInt64.ofNat x) (.cons (UInt64.ofNat c) .nil))) =
      quadraticNat.eval natModel (.cons x (.cons c .nil)) := by
  exact natToWord_fieldImage_correct quadraticField
    (.cons (⟨x, hx⟩ : Field17) (.cons (⟨c, hc⟩ : Field17) .nil))

end Witgen.Demo
