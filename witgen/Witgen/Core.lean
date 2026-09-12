import Std

/-! Open, intrinsically scoped, finite feature IR. No concrete sort or feature
is built in. Extension operation payloads must themselves be reifiable. -/
namespace Witgen

structure RegionShape (S : Type) where
  inputs : List S
  output : S

abbrev Signature (S : Type) := List S → List (RegionShape S) → S → Type

inductive HList {S : Type} (V : S → Type) : List S → Type where
  | nil : HList V []
  | cons : V s → HList V ss → HList V (s :: ss)

inductive Var {S : Type} : List S → S → Type where
  | zero : Var (s :: Γ) s
  | succ : Var Γ s → Var (t :: Γ) s

namespace Var

def index : Var Γ s → Nat
  | .zero => 0
  | .succ r => r.index + 1

def get {V : S → Type} : Var Γ s → HList V Γ → V s
  | .zero, .cons x _ => x
  | .succ r, .cons _ xs => r.get xs

end Var

namespace HList

def map {V : S → Type} {W : S → Type}
    (f : {s : S} → V s → W s) : HList V ss → HList W ss
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

end HList

mutual
  inductive Program {S : Type} (F : Signature S) : List S → S → Type where
    | ret : Var Γ t → Program F Γ t
    | let_ : F args shapes s → HList (Var Γ) args → Regions F shapes →
        Program F (s :: Γ) t → Program F Γ t
  inductive Regions {S : Type} (F : Signature S) : List (RegionShape S) → Type where
    | nil : Regions F []
    | cons : Program F sh.inputs sh.output → Regions F rest → Regions F (sh :: rest)
end

abbrev Body (V : S → Type) (sh : RegionShape S) :=
  HList V sh.inputs → V sh.output

structure Model {S : Type} (F : Signature S) (V : S → Type) where
  eval : {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → HList V args → HList (Body V) shapes → V s

mutual
  def Program.eval {F : Signature S} {V : S → Type} (M : Model F V) :
      Program F Γ t → HList V Γ → V t
    | .ret r, env => r.get env
    | .let_ op args regions next, env =>
      next.eval M (.cons (M.eval op (args.map (fun r => r.get env))
        (regions.eval M)) env)
  def Regions.eval {F : Signature S} {V : S → Type} (M : Model F V) :
      Regions F shapes → HList (Body V) shapes
    | .nil => .nil
    | .cons body rest => .cons (body.eval M) (rest.eval M)
end

variable {S : Type} {F G K : Signature S} {V W U : S → Type}

/-- Shape-preserving operation translation. It is data-to-data, never an IR node. -/
abbrev Handler (F G : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → G args shapes s

def Handler.id (F : Signature S) : Handler F F := fun op => op

def Handler.comp (h : Handler F G) (k : Handler G K) : Handler F K :=
  fun op => k (h op)

abbrev SigSum (F G : Signature S) : Signature S :=
  fun args shapes s => Sum (F args shapes s) (G args shapes s)

class Has (F G : Signature S) where
  inject : Handler F G
  injective : ∀ {args shapes s}, Function.Injective (inject (args := args) (shapes := shapes) (s := s))

instance : Has F F where
  inject := fun op => op
  injective := fun h => h

instance : Has F (SigSum F G) where
  inject := Sum.inl
  injective := fun h => Sum.inl.inj h

instance : Has G (SigSum F G) where
  inject := Sum.inr
  injective := fun h => Sum.inr.inj h

def Model.sum (M : Model F V) (N : Model G V) : Model (SigSum F G) V where
  eval := fun op args bodies => match op with
    | .inl x => M.eval x args bodies
    | .inr x => N.eval x args bodies

mutual
  def Program.mapHandler (h : Handler F G) : Program F Γ t → Program G Γ t
    | .ret r => .ret r
    | .let_ op args regions next =>
      .let_ (h op) args (regions.mapHandler h) (next.mapHandler h)
  def Regions.mapHandler (h : Handler F G) : Regions F shapes → Regions G shapes
    | .nil => .nil
    | .cons body rest => .cons (body.mapHandler h) (rest.mapHandler h)
end

/-- Simultaneous typed reference substitution, possibly non-injective. -/
abbrev RefSubst (Γ Δ : List S) := {s : S} → Var Γ s → Var Δ s

def RefSubst.lift (σ : RefSubst Γ Δ) : RefSubst (t :: Γ) (t :: Δ)
  | _, .zero => .zero
  | _, .succ r => .succ (σ r)

def Program.subst (σ : RefSubst Γ Δ) : Program F Γ t → Program F Δ t
  | .ret r => .ret (σ r)
  | .let_ op args regions next =>
    .let_ op (args.map σ) regions (next.subst σ.lift)

/-- Regions are explicitly closed over their declared inputs, so ambient
reference substitution does not touch them. -/
theorem HList.map_get_subst {V : S → Type} (σ : RefSubst Γ Δ)
    (env : HList V Γ) (env' : HList V Δ)
    (h : ∀ {s} (r : Var Γ s), (σ r).get env' = r.get env)
    (args : HList (Var Γ) ts) :
    (args.map σ).map (fun r => r.get env') = args.map (fun r => r.get env) := by
  induction args with
  | nil => rfl
  | cons r rs ih => simp only [HList.map, h r, ih]

theorem Program.eval_subst (M : Model F V) (p : Program F Γ t)
    (σ : RefSubst Γ Δ) (env : HList V Γ) (env' : HList V Δ)
    (h : ∀ {s} (r : Var Γ s), (σ r).get env' = r.get env) :
    (p.subst σ).eval M env' = p.eval M env := by
  cases p with
  | ret r => exact h r
  | let_ op args regions next =>
    simp only [Program.subst, Program.eval, HList.map_get_subst σ env env' h]
    apply Program.eval_subst M next σ.lift
    intro s r
    cases r with
    | zero => rfl
    | succ r => exact h r

/-- A relation on typed environments (and, separately, typed body lists). -/
def HList.Rel {V W : S → Type} (R : ∀ s, V s → W s → Prop) :
    HList V ts → HList W ts → Prop
  | .nil, .nil => True
  | .cons x xs, .cons y ys => R _ x y ∧ HList.Rel R xs ys

def BodyRel {V W : S → Type} (R : ∀ s, V s → W s → Prop)
    (sh : RegionShape S) (f : Body V sh) (g : Body W sh) : Prop :=
  ∀ xs ys, HList.Rel R xs ys → R sh.output (f xs) (g ys)

/-- Local feature contract: related arguments and extensionally related
higher-order bodies must produce related outputs. -/
def Model.Respects (M : Model F V) (N : Model G W)
    (h : Handler F G) (R : ∀ s, V s → W s → Prop) : Prop :=
  ∀ {args shapes s} (op : F args shapes s) xs ys fs gs,
    HList.Rel R xs ys → HList.Rel (BodyRel R) fs gs →
    R s (M.eval op xs fs) (N.eval (h op) ys gs)

theorem Var.get_related (R : ∀ s, V s → W s → Prop)
    (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys)
    (r : Var Γ t) : R t (r.get xs) (r.get ys) := by
  induction r with
  | zero => cases xs; cases ys; exact hr.1
  | succ r ih => cases xs; cases ys; exact ih _ _ hr.2

theorem HList.map_get_related (R : ∀ s, V s → W s → Prop)
    (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys)
    (args : HList (Var Γ) ts) :
    HList.Rel R (args.map (fun r => r.get xs)) (args.map (fun r => r.get ys)) := by
  induction args with
  | nil => trivial
  | cons r rs ih => exact ⟨r.get_related R xs ys hr, ih⟩

mutual
  theorem Program.eval_mapHandler_related (h : Handler F G)
      (M : Model F V) (N : Model G W) (R : ∀ s, V s → W s → Prop)
      (law : M.Respects N h R) (p : Program F Γ t)
      (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys) :
      R t (p.eval M xs) ((p.mapHandler h).eval N ys) := by
    cases p with
    | ret r => exact r.get_related R xs ys hr
    | let_ op args regions next =>
      apply Program.eval_mapHandler_related h M N R law next
      exact ⟨law op _ _ _ _ (HList.map_get_related R xs ys hr args)
        (Regions.eval_mapHandler_related h M N R law regions), hr⟩
  theorem Regions.eval_mapHandler_related (h : Handler F G)
      (M : Model F V) (N : Model G W) (R : ∀ s, V s → W s → Prop)
      (law : M.Respects N h R) (regions : Regions F shapes) :
      HList.Rel (BodyRel R) (regions.eval M) ((regions.mapHandler h).eval N) := by
    cases regions with
    | nil => trivial
    | cons body rest =>
      exact ⟨fun xs ys hr => Program.eval_mapHandler_related h M N R law body xs ys hr,
        Regions.eval_mapHandler_related h M N R law rest⟩
end

/-- A certified syntax transformation; unlike IR syntax, this compilation-time
object may contain Lean functions. The relation exposes representation/range
conditions instead of assuming all representations are interchangeable. -/
structure CertifiedLowering (M : Model F V) (N : Model G W)
    (R : ∀ s, V s → W s → Prop) where
  run : {Γ : List S} → {t : S} → Program F Γ t → Program G Γ t
  correct : ∀ {Γ t} (p : Program F Γ t) xs ys, HList.Rel R xs ys →
    R t (p.eval M xs) ((run p).eval N ys)

def CertifiedLowering.ofHandler (M : Model F V) (N : Model G W)
    (h : Handler F G) (R : ∀ s, V s → W s → Prop)
    (law : M.Respects N h R) : CertifiedLowering M N R where
  run := fun p => p.mapHandler h
  correct := Program.eval_mapHandler_related h M N R law

def RelComp (R : ∀ s, V s → W s → Prop) (Q : ∀ s, W s → U s → Prop)
    (s : S) (x : V s) (z : U s) : Prop := ∃ y, R s x y ∧ Q s y z

theorem HList.relComp_factor (R : ∀ s, V s → W s → Prop)
    (Q : ∀ s, W s → U s → Prop) (xs : HList V ts) (zs : HList U ts)
    (h : HList.Rel (RelComp R Q) xs zs) :
    ∃ ys, HList.Rel R xs ys ∧ HList.Rel Q ys zs := by
  induction xs with
  | nil => cases zs; exact ⟨.nil, trivial, trivial⟩
  | cons x xs ih =>
    cases zs with
    | cons z zs =>
      obtain ⟨y, hxy, hyz⟩ := h.1
      obtain ⟨ys, hxys, hyzs⟩ := ih zs h.2
      exact ⟨.cons y ys, ⟨hxy, hxys⟩, ⟨hyz, hyzs⟩⟩

variable {M : Model F V} {N : Model G W} {P : Model K U}
  {R : ∀ s, V s → W s → Prop} {Q : ∀ s, W s → U s → Prop}

def CertifiedLowering.comp
    (a : CertifiedLowering M N R) (b : CertifiedLowering N P Q) :
    CertifiedLowering M P (RelComp R Q) where
  run := fun p => b.run (a.run p)
  correct := by
    intro Γ t p xs zs hr
    obtain ⟨ys, hxy, hyz⟩ := HList.relComp_factor R Q xs zs hr
    exact ⟨(a.run p).eval N ys, a.correct p xs ys hxy, b.correct (a.run p) ys zs hyz⟩

theorem CertifiedLowering.comp_correct
    (a : CertifiedLowering M N R) (b : CertifiedLowering N P Q)
    (p : Program F Γ t) xs zs (hr : HList.Rel (RelComp R Q) xs zs) :
    RelComp R Q t (p.eval M xs) (((a.comp b).run p).eval P zs) :=
  (a.comp b).correct p xs zs hr

/-- Drop a formal result binder by substituting its computed reference. -/
def RefSubst.replaceHead (r : Var Γ s) : RefSubst (s :: Γ) Γ
  | _, .zero => r
  | _, .succ x => x

/-- Bind is syntax composition, not a runtime Lean continuation. Extra lets in
`p` weaken the original continuation immediately below its result binder. -/
def Program.bind (p : Program F Γ s) (next : Program F (s :: Γ) t) : Program F Γ t :=
  match p with
  | .ret r => next.subst (RefSubst.replaceHead r)
  | .let_ op args regions tail =>
    .let_ op args regions (tail.bind (next.subst (RefSubst.lift (fun r => .succ r))))

theorem Program.eval_bind (M : Model F V) (p : Program F Γ s)
    (next : Program F (s :: Γ) t) (env : HList V Γ) :
    (p.bind next).eval M env = next.eval M (.cons (p.eval M env) env) := by
  cases p with
  | ret r =>
    apply Program.eval_subst
    intro t x
    cases x <;> rfl
  | let_ op args regions tail =>
    simp only [Program.bind, Program.eval, Program.eval_bind M tail]
    apply Program.eval_subst
    intro t x
    cases x <;> rfl

/-- Lookup commutes with pointwise interpretation of an argument vector. -/
theorem Var.get_map (f : {s : S} → V s → W s) (r : Var Γ t) (xs : HList V Γ) :
    r.get (xs.map f) = f (r.get xs) := by
  induction r with
  | zero => cases xs; rfl
  | succ r ih => cases xs; exact ih _

/-- A closed, typed target subprogram for an operation. The target region syntax
is available to the template; no semantic body function is inserted into IR. -/
abbrev Template (F G : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → Regions G shapes → Program G args s

mutual
  def Program.lower (template : Template F G) : Program F Γ t → Program G Γ t
    | .ret r => .ret r
    | .let_ op args regions next =>
      ((template op (regions.lower template)).subst (fun r => r.get args)).bind
        (next.lower template)
  def Regions.lower (template : Template F G) : Regions F shapes → Regions G shapes
    | .nil => .nil
    | .cons body rest => .cons (body.lower template) (rest.lower template)
end

/-- Higher-order template contract. A source operation can become many target
operations, with arbitrary target internals but the same typed formal interface. -/
def Template.Respects (M : Model F V) (N : Model G W)
    (template : Template F G) (R : ∀ s, V s → W s → Prop) : Prop :=
  ∀ {args shapes s} (op : F args shapes s) xs ys fs (regions : Regions G shapes),
    HList.Rel R xs ys → HList.Rel (BodyRel R) fs (regions.eval N) →
    R s (M.eval op xs fs) ((template op regions).eval N ys)

mutual
  theorem Program.eval_lower_related (template : Template F G)
      (M : Model F V) (N : Model G W) (R : ∀ s, V s → W s → Prop)
      (law : Template.Respects M N template R) (p : Program F Γ t)
      (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys) :
      R t (p.eval M xs) ((p.lower template).eval N ys) := by
    cases p with
    | ret r => exact r.get_related R xs ys hr
    | let_ op args regions next =>
      simp only [Program.lower, Program.eval_bind, Program.eval]
      apply Program.eval_lower_related template M N R law next
      constructor
      · have inst := Program.eval_subst N (template op (regions.lower template))
          (fun r => r.get args) (args.map (fun r => r.get ys)) ys
          (fun r => (r.get_map (fun v => v.get ys) args).symm)
        rw [inst]
        exact law op _ _ _ _ (HList.map_get_related R xs ys hr args)
          (Regions.eval_lower_related template M N R law regions)
      · exact hr
  theorem Regions.eval_lower_related (template : Template F G)
      (M : Model F V) (N : Model G W) (R : ∀ s, V s → W s → Prop)
      (law : Template.Respects M N template R) (regions : Regions F shapes) :
      HList.Rel (BodyRel R) (regions.eval M) ((regions.lower template).eval N) := by
    cases regions with
    | nil => trivial
    | cons body rest =>
      exact ⟨fun xs ys hr => Program.eval_lower_related template M N R law body xs ys hr,
        Regions.eval_lower_related template M N R law rest⟩
end

def CertifiedLowering.ofTemplate (M : Model F V) (N : Model G W)
    (template : Template F G) (R : ∀ s, V s → W s → Prop)
    (law : Template.Respects M N template R) : CertifiedLowering M N R where
  run := fun p => p.lower template
  correct := Program.eval_lower_related template M N R law

end Witgen
