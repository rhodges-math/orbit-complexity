import OrbitComplexity.FrobeniusSplitting.Normality.GraphElements
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # The coefficient stages above a prescribed finite base -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- Coefficient stages retain the entire prescribed subalgebra. -/
def CoefficientStage {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :=
  {R : Subalgebra ℤ K // R.FG ∧ S ≤ R}

/-- Coefficient stages are ordered by inclusion of subalgebras. -/
instance {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    PartialOrder (CoefficientStage S) := inferInstanceAs
      (PartialOrder {R : Subalgebra ℤ K // R.FG ∧ S ≤ R})

/-- Coefficient stages form a directed order under the subalgebra supremum. -/
instance {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    IsDirectedOrder (CoefficientStage S) where
  directed i j := by
    refine ⟨⟨i.val ⊔ j.val, i.property.1.sup j.property.1,
      i.property.2.trans le_sup_left⟩, ?_, ?_⟩
    · change i.val ≤ i.val ⊔ j.val
      exact le_sup_left
    · change j.val ≤ i.val ⊔ j.val
      exact le_sup_right

/-- All transition maps are the original coefficient inclusions. -/
def coefficientRings {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    CoefficientStage S ⥤ CommRingCat.{u} where
  obj i := .of i.val
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The given coefficient ring is the apex, with its inclusion maps. -/
def coefficientCocone {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    Cocone (coefficientRings S) where
  pt := .of K
  ι :=
    { app := fun i => CommRingCat.ofHom (algebraMap i.val K)
      naturality := fun _ _ _ => by ext x; rfl }

/-- The union of the finitely generated coefficient stages is the full
coefficient ring, as a colimit of commutative rings. -/
def coefficientColimit {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) : IsColimit (coefficientCocone S) := by
  letI : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  have htypes : IsColimit ((forget CommRingCat).mapCocone (coefficientCocone S)) := by
    apply Types.FilteredColimit.isColimitOf
    · intro x
      let R := S ⊔ Algebra.adjoin ℤ ({x} : Set K)
      have hR : R.FG := hS.sup
        (Subalgebra.fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩)
      have hx : x ∈ R := (le_sup_right : Algebra.adjoin ℤ ({x} : Set K) ≤ R)
        (Algebra.subset_adjoin (Set.mem_singleton x))
      exact ⟨⟨R, hR, le_sup_left⟩, ⟨x, hx⟩, rfl⟩
    · intro i j xi xj h
      let k : CoefficientStage S := ⟨i.val ⊔ j.val, i.property.1.sup j.property.1,
        i.property.2.trans le_sup_left⟩
      have hik : i ≤ k := by
        change i.val ≤ i.val ⊔ j.val
        exact le_sup_left
      have hjk : j ≤ k := by
        change j.val ≤ i.val ⊔ j.val
        exact le_sup_right
      refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
      apply Subtype.ext
      exact h
  letI : ReflectsColimit (coefficientRings S) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget CommRingCat) htypes

/-- The coefficient-scheme diagram uses the original spectra and Spec maps. -/
def coefficientSchemes {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    (CoefficientStage S)ᵒᵖ ⥤ Scheme.{u} :=
  (coefficientRings S).op ⋙ Scheme.Spec

/-- The cone has the Spec K as its apex. -/
def coefficientSpecCone {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    Cone (coefficientSchemes S) :=
  Scheme.Spec.mapCone (coefficientCocone S).op

/-- Spec K is the inverse limit of the specified coefficient stages. -/
def coefficientSpecLimit {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) : IsLimit (coefficientSpecCone S) :=
  isLimitOfPreserves Scheme.Spec (coefficientColimit S hS).op


end FrobeniusSplitting
