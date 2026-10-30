import OrbitComplexity.FrobeniusSplitting.Normality.NormalizationOpen
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Birationality from an isomorphism over a dense open

A morphism that restricts to an isomorphism over a dense target open determines
a partial isomorphism when its source is irreducible. The partial isomorphism
agrees with the morphism and respects any base map on the target. Applying this
to finite normalization gives birationality over the base.

## Main definitions

* `FrobeniusSplitting.IsIsoOverDense.partialIso`: the induced partial isomorphism.

## Main results

* `FrobeniusSplitting.IsIsoOverDense.partialIso_fac`: agreement with the morphism.
* `FrobeniusSplitting.normalization_birationalOver`: birationality of normalization.
-/

noncomputable section

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory

universe u

/-- An isomorphism over a dense target open determines a partial isomorphism. -/
def IsIsoOverDense.partialIso {X Y : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} (h : IsIsoOverDense f) : Scheme.PartialIso X Y := by
  let U := h.choose
  have hdense : Dense (U : Set Y) := h.choose_spec.1
  have : IsIso (f ∣_ U) := h.choose_spec.2
  have : Nonempty Y := Nonempty.map f inferInstance
  have hnonempty : (U : Set Y).Nonempty := hdense.nonempty
  have hpreimage : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hnonempty
    let x := inv (f ∣_ U) ⟨y, hy⟩
    exact ⟨x.1, x.2⟩
  exact ⟨f ⁻¹ᵁ U, (f ⁻¹ᵁ U).isOpen.dense hpreimage, U, hdense, asIso (f ∣_ U)⟩

/-- The partial isomorphism obtained from a morphism agrees with it on its source. -/
theorem IsIsoOverDense.partialIso_fac {X Y : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} (h : IsIsoOverDense f) :
    h.partialIso.source.ι ≫ f = h.partialIso.iso.hom ≫ h.partialIso.target.ι :=
  (morphismRestrict_ι f h.choose).symm

/-- A morphism that is an isomorphism over a dense open gives birational schemes. -/
theorem IsIsoOverDense.birational {X Y : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} (h : IsIsoOverDense f) : Scheme.Birational X Y :=
  ⟨h.partialIso⟩

/-- The induced partial isomorphism preserves every base morphism of the target. -/
theorem IsIsoOverDense.birationalOver {S X Y : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} (h : IsIsoOverDense f) (base : Y ⟶ S) :
    Scheme.BirationalOver (f ≫ base) base := by
  refine ⟨h.partialIso, ?_⟩
  exact (by simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ base) h.partialIso_fac.symm)

end FrobeniusSplitting
