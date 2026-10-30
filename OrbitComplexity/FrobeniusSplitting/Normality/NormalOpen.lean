import OrbitComplexity.FrobeniusSplitting.Normality.NormalizationOpen

/-!
# Normal local rings on dense open subsets

An isomorphism over a dense open subset transfers normal local rings from its
source. Applied to finite normalization, this gives a dense open subset with
normal local rings in every affine integral variety over a field.

## Main results

* `FrobeniusSplitting.IsIsoOverDense.exists_normal_open`: descent on a dense open.
* `FrobeniusSplitting.exists_normal_open_affine`: a dense normal open in an affine variety.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory

universe u

/-- Normal local rings descend across an isomorphism over a dense open subset. -/
theorem IsIsoOverDense.exists_normal_open {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : IsIsoOverDense f)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧
      ∀ y : U, IsDomain (Y.presheaf.stalk y.1) ∧ IsIntegrallyClosed (Y.presheaf.stalk y.1) := by
  obtain ⟨U, hdense, hiso⟩ := h
  have : IsIso (f ∣_ U) := hiso
  refine ⟨U, hdense, ?_⟩
  intro y
  let z := inv (f ∣_ U) y
  have hinv : IsIso (inv (f ∣_ U)) := inferInstance
  have : IsIso ((inv (f ∣_ U)).stalkMap y) :=
    ((isIso_iff_isIso_stalkMap (inv (f ∣_ U))).mp hinv).2 y
  let e₁ := (asIso ((f ⁻¹ᵁ U).ι.stalkMap z)).commRingCatIsoToRingEquiv
  let e₂ := (asIso ((inv (f ∣_ U)).stalkMap y)).commRingCatIsoToRingEquiv
  let e₃ := (U.stalkIso y).commRingCatIsoToRingEquiv
  let e := e₁.trans (e₂.trans e₃)
  have : IsDomain (X.presheaf.stalk ((f ⁻¹ᵁ U).ι z)) := (hX ((f ⁻¹ᵁ U).ι z)).1
  have : IsIntegrallyClosed (X.presheaf.stalk ((f ⁻¹ᵁ U).ι z)) := (hX ((f ⁻¹ᵁ U).ι z)).2
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end FrobeniusSplitting
