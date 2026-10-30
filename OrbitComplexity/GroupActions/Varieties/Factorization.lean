import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Factorization from reduced schemes

A morphism from a reduced scheme factors through a preimmersion whenever its image lies
inside the preimmersion's image. Pulling back the preimmersion gives a surjective closed
immersion into a reduced scheme, and hence an isomorphism.

## Main definitions

* `GroupActions.liftPreimmersion`: factorization from a reduced scheme through a preimmersion.

## Main results

* `GroupActions.liftPreimmersion_fac`: composition with the preimmersion recovers the morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (f : Y ⟶ X) [IsPreimmersion i] [IsReduced Y]

private theorem pullback_fst_isIso (himage : Set.range f ⊆ Set.range i) :
    IsIso (pullback.fst f i) := by
  have hrange : Set.range (pullback.fst f i) = Set.univ := by
    rw [Scheme.Pullback.range_fst]
    exact Set.preimage_eq_univ_iff.mpr himage
  have : Surjective (pullback.fst f i) := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsClosedImmersion (pullback.fst f i) :=
    .of_isPreimmersion _ (hrange ▸ isClosed_univ)
  exact isIso_of_isClosedImmersion_of_surjective _

/-- A morphism from a reduced scheme factors through a preimmersion containing its image. -/
def liftPreimmersion (himage : Set.range f ⊆ Set.range i) : Y ⟶ Z :=
  letI := pullback_fst_isIso i f himage
  inv (pullback.fst f i) ≫ pullback.snd f i

/-- Composition of the factorization with the preimmersion is the original morphism. -/
theorem liftPreimmersion_fac (himage : Set.range f ⊆ Set.range i) :
    liftPreimmersion i f himage ≫ i = f := by
  let := pullback_fst_isIso i f himage
  change (inv (pullback.fst f i) ≫ pullback.snd f i) ≫ i = f
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

end

end GroupActions
