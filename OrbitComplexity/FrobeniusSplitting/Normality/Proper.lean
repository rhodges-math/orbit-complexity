import OrbitComplexity.FrobeniusSplitting.Normality.SchemeLift
import OrbitComplexity.FrobeniusSplitting.Normality.SplitNormal
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth
import OrbitComplexity.FrobeniusSplitting.Normality.Stalk

/-!
# Normality under proper morphisms with connected fibers

A proper map from a normal integral source lifts dominantly to the finite
normalization of its affine target. Properness makes the lift surjective.
Geometrically connected fibers and a Frobenius splitting then force normality.
The affine argument applies over every target affine open to give normal local rings.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- A split affine domain dominated properly with geometrically connected fibers by
a normal integral scheme is normal. -/
theorem isIntegrallyClosed_of_proper {k R : Type u} [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    {q : ℕ} [Fact q.Prime] [CharP R q] (splitting : RingSplitting R q)
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f]
    [GeometricallyConnected f]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed R := by
  obtain ⟨h, hfac, hdom⟩ := exists_normalizationLift f hn
  let C := integralClosure R (FractionRing R)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have : IsDominant h := hdom
  have := finite_normalization (k := k) (R := R)
  have : IsFinite g := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsProper (h ≫ g) := by rw [hfac]; infer_instance
  have : IsProper h := IsProper.of_comp h g
  have hrange : Set.range h = Set.univ := by
    rw [← h.isClosedMap.isClosed_range.closure_eq]
    exact h.denseRange.closure_range
  have : Surjective h := ⟨Set.range_eq_univ.mp hrange⟩
  have : GeometricallyConnected (h ≫ g) := by rw [hfac]; infer_instance
  exact isIntegrallyClosed_of_connected (k := k) splitting h

private instance connected_respectsIso : MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- A split integral target of a proper morphism with geometrically connected fibers
from a normal integral source has normal local rings. -/
theorem stalks_of_proper {K : Type u} [Field K]
    {X Y : Scheme.{u}} [IsIntegral X] [IrreducibleSpace Y]
    (base : Y ⟶ Spec (.of K)) [LocallyOfFiniteType base]
    (f : X ⟶ Y) [IsProper f] [GeometricallyConnected f]
    {q : ℕ} [Fact q.Prime] [CharP K q] (splitting : SchemeSplitting Y q)
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  have : IsReduced Y := splitting.isReduced (Fact.out : q.Prime).one_lt
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  obtain ⟨x, hx⟩ := f.surjective y
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by simpa [hx] using hyU⟩⟩
  let R := Γ(Y, U)
  let e := Scheme.ΓSpecIso (.of K)
  let φ : K →+* R := (base.appLE ⊤ U le_top).hom.comp e.inv.hom
  let : Algebra K R := φ.toAlgebra
  have hφ : φ.FiniteType := (base.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    e.symm.commRingCatIsoToRingEquiv.finite.finiteType
  have : Algebra.FiniteType K R := hφ
  have : CharP R q := charP_sections base U
  let f' := (f ∣_ U) ≫ hU.isoSpec.hom
  have : IsProper f' := inferInstance
  have : GeometricallyConnected f' :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
      (f ∣_ U) hU.isoSpec.hom).mpr inferInstance
  have hsource : ∀ z : (f ⁻¹ᵁ U).toScheme,
      IsIntegrallyClosed ((f ⁻¹ᵁ U).toScheme.presheaf.stalk z) := by
    intro z
    have := hn ((f ⁻¹ᵁ U).ι z)
    exact IsIntegrallyClosed.of_equiv
      (asIso ((f ⁻¹ᵁ U).ι.stalkMap z)).commRingCatIsoToRingEquiv
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_proper (k := K)
    (splitting.onOpen U) f' hsource
  exact ⟨inferInstance, isIntegrallyClosed_stalk hU hyU⟩

end FrobeniusSplitting
