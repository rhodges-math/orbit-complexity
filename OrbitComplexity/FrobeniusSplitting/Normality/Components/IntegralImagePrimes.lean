import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Batteries.Tactic.Lint

/-! # Prime affine image ideals

An integral source gives a prime image ideal on each affine open that it meets.
The image ideal is the unit ideal on an affine open with empty preimage.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory

namespace FrobeniusSplitting

/-- A scheme-theoretically dominant quasi-compact morphism from an integral
scheme has integral target. -/
theorem integral_of_scheme_dominant {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    IsIntegral Y := by
  have himage : IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn)
  have hwhole : IsIrreducible (Set.univ : Set Y) := by
    rw [← f.denseRange.closure_range]
    exact himage.closure
  have : IrreducibleSpace Y := by
    rw [irreducibleSpace_def]
    exact hwhole
  have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced f
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

private theorem empty_sections {X : Scheme.{u}} (U : X.Opens) (h : U = ⊥) :
    Subsingleton Γ(X, U) := by
  cases h
  infer_instance

private theorem ker_ideal_top_or_prime {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = ⊤ ∨ (f.ker.ideal U).IsPrime := by
  classical
  rw [Scheme.Hom.ker_apply f U]
  by_cases h : f ⁻¹ᵁ U.1 = ⊥
  · left
    let : Subsingleton Γ(X, f ⁻¹ᵁ U.1) := empty_sections _ h
    exact RingHom.ker_eq_top_of_subsingleton (f.app U.1).hom
  · right
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h
    let : Nonempty (f ⁻¹ᵁ U.1) := ⟨⟨x, hx⟩⟩
    exact RingHom.ker_isPrime (f.app U.1).hom

/-- An integral endpoint source and equality of image kernels give unit or
prime affine ideals for the same ambient immersion. -/
theorem image_ideal_top_or_prime {X Y Z : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (j : Y ⟶ Z) [QuasiCompact (f ≫ j)]
    (hker : (f ≫ j).ker = j.ker) (U : Z.affineOpens) :
    j.ker.ideal U = ⊤ ∨ (j.ker.ideal U).IsPrime := by
  have hp := ker_ideal_top_or_prime (f ≫ j) U
  exact hker ▸ hp

end FrobeniusSplitting
