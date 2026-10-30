import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.CoefficientLimit
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.SurjectiveStages
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarMaps

/-! # Closed affine morphisms at a coefficient stage

A finite family of morphisms between affine schemes, with finite type sources,
which becomes a family of closed immersions over a field is already a family
of closed immersions at one finite coefficient stage.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

universe u v

/-- The morphism between two scalar pullbacks induced by a morphism over their
common base. -/
def affineScalarMap {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    pullback κ X.hom ⟶ pullback κ Y.hom :=
  pullback.map κ X.hom κ Y.hom (𝟙 T) f.left (𝟙 B)
    (by simp) (by simp)

private theorem section_finiteType
    {S : Type u} [CommRing S] {X : Scheme.{u}} [IsAffine X]
    (s : X ⟶ Spec (.of S)) [LocallyOfFiniteType s] :
    let : Algebra S Γ(X, ⊤) :=
      (s.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    Algebra.FiniteType S Γ(X, ⊤) := by
  let : Algebra S Γ(X, ⊤) :=
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  apply RingHom.finiteType_algebraMap.mp
  exact (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) s inferInstance).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).inv).2)

private theorem scalarMap_surjective_iff
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    (X Y : Over (Spec (.of S))) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) :
    letI : Algebra S Γ(X.left, ⊤) :=
      (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : Algebra S Γ(Y.left, ⊤) :=
      (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    Function.Surjective
      (Algebra.TensorProduct.lTensor (S := R) R
        (affineSectionMap X.hom Y.hom f.left f.w)) ↔
      Function.Surjective
        (affineScalarMap (Spec.map (CommRingCat.ofHom (algebraMap S R))) f).appTop.hom := by
  exact affine_scalar_map_surjective X.hom Y.hom f.left f.w
    (pullback.fst _ X.hom) (pullback.fst _ Y.hom)
    (pullback.snd _ X.hom) (pullback.snd _ Y.hom)
    (IsPullback.of_hasPullback _ X.hom).flip
    (IsPullback.of_hasPullback _ Y.hom).flip
    (affineScalarMap (Spec.map (CommRingCat.ofHom (algebraMap S R))) f)
    (by simp [affineScalarMap]) (by simp [affineScalarMap])

private theorem scalarMap_closed_iff
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    (X Y : Over (Spec (.of S))) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) :
    letI : Algebra S Γ(X.left, ⊤) :=
      (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : Algebra S Γ(Y.left, ⊤) :=
      (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    IsClosedImmersion
      (affineScalarMap (Spec.map (CommRingCat.ofHom (algebraMap S R))) f) ↔
      Function.Surjective
        (Algebra.TensorProduct.lTensor (S := R) R
          (affineSectionMap X.hom Y.hom f.left f.w)) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let g := affineScalarMap κ f
  constructor
  · intro hg
    let : IsClosedImmersion g := hg
    exact (scalarMap_surjective_iff X Y f).mpr
      (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  · intro hg
    exact IsClosedImmersion.of_surjective_of_isAffine g
      ((scalarMap_surjective_iff X Y f).mp hg)

/-- Finitely many affine morphisms with finite type sources which become closed
immersions over a field become closed immersions at one coefficient stage above
a prescribed starting stage. -/
theorem exists_closed_affine_stage
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Finite I]
    (X Y : I → Over (Spec (.of S)))
    [∀ i, IsAffine (X i).left] [∀ i, IsAffine (Y i).left]
    [∀ i, LocallyOfFiniteType (X i).hom]
    (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, IsClosedImmersion
      (affineScalarMap (Spec.map (CommRingCat.ofHom (algebraMap S K))) (f i)))
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S), start ≤ j ∧ ∀ i,
      IsClosedImmersion
        (affineScalarMap
          (Spec.map (CommRingCat.ofHom
            (Subalgebra.inclusion j.property.2).toRingHom)) (f i)) := by
  let (i : I) : Algebra S Γ((X i).left, ⊤) :=
    ((X i).hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let (i : I) : Algebra S Γ((Y i).left, ⊤) :=
    ((Y i).hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let (i : I) : Algebra.FiniteType S Γ((X i).left, ⊤) :=
    section_finiteType (X i).hom
  let g (i : I) : Γ((Y i).left, ⊤) →ₐ[S] Γ((X i).left, ⊤) :=
    affineSectionMap (X i).hom (Y i).hom (f i).left (f i).w
  have hg (i : I) : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id K K) (g i)) :=
    (scalarMap_closed_iff (X i) (Y i) (f i)).mp (hf i)
  obtain ⟨R, hSR, hR, hstart, hsurj⟩ :=
    exists_surjective_family_stage S hS
      (fun i => Γ((Y i).left, ⊤)) (fun i => Γ((X i).left, ⊤))
      g hg start.val start.property.1
  let j : CoefficientStage S := ⟨R, hR, hSR⟩
  refine ⟨j, hstart, fun i => ?_⟩
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  exact (scalarMap_closed_iff (R := R) (X i) (Y i) (f i)).mpr (hsurj i)

end FrobeniusSplitting
