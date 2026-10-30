import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorPatchCoordinates
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # principal patches from the prior-model cover -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem eval_square {P X Y Z : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : a ≫ f = b ≫ g) (x : P) : f (a x) = g (b x) :=
  (Scheme.Hom.comp_apply a f x).symm.trans
    ((congrArg (fun z : P ⟶ Z ↦ z x) h).trans (Scheme.Hom.comp_apply b g x))

private theorem affine_principal_cover (P : Scheme.{u}) [IsAffine P] (V : P.OpenCover.{u}) :
    ∃ (L : Type u) (_ : Finite L) (j : L → V.I₀) (s : L → Γ(P, ⊤)),
      (∀ l, P.basicOpen (s l) ≤ (V.f (j l)).opensRange) ∧
        ∀ x : P, ∃ l, x ∈ P.basicOpen (s l) := by
  classical
  have H (x : P) : ∃ (j : V.I₀) (s : Γ(P, ⊤)),
      x ∈ P.basicOpen s ∧ P.basicOpen s ≤ (V.f j).opensRange := by
    obtain ⟨j, y, hy⟩ := V.exists_eq x
    have hx : x ∈ (V.f j).opensRange := ⟨y, hy⟩
    obtain ⟨_, ⟨s, rfl⟩, hxs, hle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen P) hx
    exact ⟨j, s, hxs, hle⟩
  choose j s hxs hle using H
  obtain ⟨l, hl⟩ := isCompact_univ.elim_finite_subcover
    (fun x : P ↦ (P.basicOpen (s x) : Set P)) (fun x ↦ (P.basicOpen (s x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxs x⟩)
  refine ⟨l, inferInstance, (fun x ↦ j x.val), (fun x ↦ s x.val),
    (fun x ↦ hle x.val), fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hl (Set.mem_univ x))
  obtain ⟨hal, hxa⟩ := Set.mem_iUnion.mp ha
  exact ⟨⟨a, hal⟩, hxa⟩

/-- The prior affine cover gives finite principal patches factoring through the same
endpoint cover, with scheme maps and coverage. -/
theorem exists_prior_patches {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {Y YK : Scheme.{u}}
    (base : Y ⟶ Spec (.of R)) (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ i, IsAffine (U.X i))
    (V : YK.OpenCover.{u}) :
    let Q : YK.OpenCover.{u} := U.pullback₂ qY
    ∃ (L : Type u) (_ : Finite L) (prior : L → U.I₀) (endpoint : L → V.I₀)
      (s : ∀ l, Γ(Q.X (prior l), ⊤))
      (a : ∀ l, ((Q.X (prior l)).basicOpen (s l)).toScheme ⟶ V.X (endpoint l)),
      (∀ l, ((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l) = a l ≫ V.f (endpoint l)) ∧
      ∀ y : YK, ∃ l, ∃ z : ((Q.X (prior l)).basicOpen (s l)).toScheme,
        (((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l)) z = y := by
  classical
  let Q : YK.OpenCover.{u} := U.pullback₂ qY
  let (i : U.I₀) : IsAffine (U.X i) := hU i
  let (i : U.I₀) : IsAffine (Q.X i) :=
    IsAffine.of_isPullback ((IsPullback.of_hasPullback (U.f i) qY).paste_vert h)
  choose L finiteL endpoint s hle hcover using fun i : U.I₀ ↦
    affine_principal_cover (Q.X i) (V.pullback₁ (Q.f i))
  let (i : U.I₀) : Finite (L i) := finiteL i
  let A := Σ i : U.I₀, L i
  have hrange (l : A) : Set.range
      (((Q.X l.1).basicOpen (s l.1 l.2)).ι ≫ Q.f l.1) ⊆
        Set.range (V.f (endpoint l.1 l.2)) := by
    rintro y ⟨z, rfl⟩
    have hz : z.val ∈ ((V.pullback₁ (Q.f l.1)).f (endpoint l.1 l.2)).opensRange :=
      hle l.1 l.2 z.property
    obtain ⟨x, hx⟩ := hz
    refine ⟨(pullback.snd (Q.f l.1) (V.f (endpoint l.1 l.2))) x, ?_⟩
    have he := eval_square (pullback.fst (Q.f l.1) (V.f (endpoint l.1 l.2)))
      (pullback.snd (Q.f l.1) (V.f (endpoint l.1 l.2)))
      (Q.f l.1) (V.f (endpoint l.1 l.2))
      (pullback.condition (f := Q.f l.1) (g := V.f (endpoint l.1 l.2))) x
    exact he.symm.trans (congrArg (fun y ↦ Q.f l.1 y) hx)
  let a (l : A) : ((Q.X l.1).basicOpen (s l.1 l.2)).toScheme ⟶
      V.X (endpoint l.1 l.2) := by
    have : IsOpenImmersion (V.f (endpoint l.1 l.2)) := V.map_prop _
    exact IsOpenImmersion.lift (V.f (endpoint l.1 l.2))
      (((Q.X l.1).basicOpen (s l.1 l.2)).ι ≫ Q.f l.1) (hrange l)
  refine ⟨A, inferInstance, (fun l ↦ l.1), (fun l ↦ endpoint l.1 l.2),
    (fun l ↦ s l.1 l.2), a, ?_, ?_⟩
  · intro l
    have : IsOpenImmersion (V.f (endpoint l.1 l.2)) := V.map_prop _
    exact (IsOpenImmersion.lift_fac _ _ (hrange l)).symm
  · intro y
    obtain ⟨i, x, hx⟩ := Q.exists_eq y
    obtain ⟨l, hl⟩ := hcover i x
    exact ⟨⟨i, l⟩, ⟨x, hl⟩, hx⟩

end FrobeniusSplitting
