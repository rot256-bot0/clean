import Witgen.Core

namespace Witgen
variable {S : Type} {F G : Signature S} {V W : S → Type}

/-- An operation implementation can explicitly decline unsupported operations. -/
abbrev PartialHandler (F G : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {t : S} →
    F args shapes t → Option (G args shapes t)

mutual
  def Program.mapHandler? (h : PartialHandler F G) : Program F Γ t → Option (Program G Γ t)
    | .ret r => some (.ret r)
    | .let_ op args regions next =>
      match h op, regions.mapHandler? h, next.mapHandler? h with
      | some target, some bodies, some rest => some (.let_ target args bodies rest)
      | _, _, _ => none
  def Regions.mapHandler? (h : PartialHandler F G) : Regions F shapes → Option (Regions G shapes)
    | .nil => some .nil
    | .cons body rest =>
      match body.mapHandler? h, rest.mapHandler? h with
      | some p, some ps => some (.cons p ps)
      | _, _ => none
end

/-- Every accepted operation preserves the relation; rejection is not an
implementation, and cannot be used to certify an emitted program. -/
def PartialHandler.Respects (h : PartialHandler F G) (M : Model F V) (N : Model G W)
    (R : ∀ t, V t → W t → Prop) : Prop :=
  ∀ {args shapes t} (op : F args shapes t) (target : G args shapes t),
    h op = some target → ∀ xs ys fs gs,
    HList.Rel R xs ys → HList.Rel (BodyRel R) fs gs →
    R t (M.eval op xs fs) (N.eval target ys gs)

theorem Program.eval_mapHandler?_related (h : PartialHandler F G)
    (M : Model F V) (N : Model G W) (R : ∀ t, V t → W t → Prop)
    (law : h.Respects M N R) (p : Program F Γ t) (q : Program G Γ t)
    (accepted : p.mapHandler? h = some q)
    (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys) :
    R t (p.eval M xs) (q.eval N ys) := by
  revert q accepted xs ys hr
  induction p using Program.rec
      (motive_2 := fun shapes regions => ∀ bodies : Regions G shapes,
        regions.mapHandler? h = some bodies →
        HList.Rel (BodyRel R) (regions.eval M) (bodies.eval N)) with
  | ret r =>
    intro q accepted xs ys hr
    simp only [Program.mapHandler?, Option.some.injEq] at accepted
    cases accepted
    exact r.get_related R xs ys hr
  | let_ op args regions next ihRegions ihNext =>
    intro q accepted xs ys hr
    cases hop : h op with
    | none => simp [Program.mapHandler?, hop] at accepted
    | some target =>
      cases hb : regions.mapHandler? h with
      | none => simp [Program.mapHandler?, hop, hb] at accepted
      | some bodies =>
        cases hn : next.mapHandler? h with
        | none => simp [Program.mapHandler?, hop, hb, hn] at accepted
        | some rest =>
          simp only [Program.mapHandler?, hop, hb, hn, Option.some.injEq] at accepted
          cases accepted
          apply ihNext rest hn
          exact ⟨law op target hop _ _ _ _ (HList.map_get_related R xs ys hr args)
            (ihRegions bodies hb), hr⟩
  | nil =>
    rename_i bodies accepted
    simp only [Regions.mapHandler?, Option.some.injEq] at accepted
    cases accepted
    trivial
  | cons body rest ihBody ihRest =>
    rename_i bodies accepted
    cases hb : body.mapHandler? h with
    | none => simp [Regions.mapHandler?, hb] at accepted
    | some p =>
      cases hr : rest.mapHandler? h with
      | none => simp [Regions.mapHandler?, hb, hr] at accepted
      | some ps =>
        simp only [Regions.mapHandler?, hb, hr, Option.some.injEq] at accepted
        cases accepted
        exact ⟨fun xs ys rel => ihBody p hb xs ys rel, ihRest ps hr⟩

structure PartialCertifiedLowering (M : Model F V) (N : Model G W)
    (R : ∀ t, V t → W t → Prop) where
  run : {Γ : List S} → {t : S} → Program F Γ t → Option (Program G Γ t)
  correct : ∀ {Γ t} (p : Program F Γ t) (q : Program G Γ t), run p = some q →
    ∀ xs ys, HList.Rel R xs ys → R t (p.eval M xs) (q.eval N ys)

def PartialCertifiedLowering.ofHandler (M : Model F V) (N : Model G W)
    (h : PartialHandler F G) (R : ∀ t, V t → W t → Prop)
    (law : h.Respects M N R) : PartialCertifiedLowering M N R where
  run := fun p => p.mapHandler? h
  correct := Program.eval_mapHandler?_related h M N R law

end Witgen
