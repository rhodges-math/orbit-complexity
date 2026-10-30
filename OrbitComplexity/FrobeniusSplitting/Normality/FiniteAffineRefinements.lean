import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Finite affine cover refinements

Finite affine refinements retain their morphisms to a specified open cover.
-/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- A quasi-compact scheme has a finite affine open cover refining each specified
open cover, with a morphism retaining the refinement maps. -/
theorem exists_affine_cover_refinement {X : Scheme.{u}} [CompactSpace X]
    (𝒰 : X.OpenCover.{u}) :
    ∃ 𝒱 : X.OpenCover.{u}, Finite 𝒱.I₀ ∧
      (∀ i, IsAffine (𝒱.X i)) ∧ Nonempty (𝒱 ⟶ 𝒰) := by
  let 𝒜 := 𝒰.affineRefinement.openCover
  let 𝒱 := 𝒜.finiteSubcover
  have hfinite : Finite 𝒱.I₀ := inferInstance
  have haffine : ∀ i, IsAffine (𝒱.X i) := by
    intro i
    change IsAffine (𝒜.X (𝒜.idx i.val))
    exact Scheme.isAffine_affineOpenCover X 𝒰.affineRefinement (𝒜.idx i.val)
  let r : 𝒱 ⟶ 𝒜 :=
    { s₀ := fun i ↦ 𝒜.idx i.val
      h₀ := fun _ ↦ 𝟙 _ }
  exact ⟨𝒱, hfinite, haffine, ⟨r ≫ 𝒰.fromAffineRefinement⟩⟩

end FrobeniusSplitting
