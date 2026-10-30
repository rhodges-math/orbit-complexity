import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite affine covers and intersections

A quasi-compact scheme admits a finite affine open cover. Its nonempty finite intersections
form a restriction diagram and remain affine when the scheme has affine diagonal.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- A quasi-compact scheme has a finite affine open cover. -/
theorem exists_finite_affine_opens (X : Scheme.{u}) [CompactSpace X] :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  let 𝒰 := X.affineCover.finiteSubcover
  exact ⟨𝒰.I₀, inferInstance, (fun i ↦ (𝒰.f i).opensRange),
    (fun i ↦ isAffineOpen_opensRange (𝒰.f i)), 𝒰.iSup_opensRange⟩

variable {X : Scheme.{u}} {I : Type u}

/-- The finite intersections of a family of open subsets, ordered by reverse inclusion. -/
def intersectionOpens (U : I → X.Opens) :
    {s : Finset I // s.Nonempty}ᵒᵖ ⥤ X.Opens where
  obj s := ⨅ i ∈ s.unop.val, U i
  map {s t} f := homOfLE (by
    refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    have hmem : i ∈ s.unop.val := (leOfHom f.unop) hi
    exact iInf_le_of_le i (iInf_le _ hmem))

/-- Every nonempty finite intersection of affine opens is affine when the diagonal is affine. -/
theorem intersectionOpens_affine
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
    IsAffineOpen ((intersectionOpens U).obj s) := by
  exact IsAffineOpen.biInf (s.unop.val : Set I) s.unop.val.finite_toSet
    (Finset.coe_nonempty.mpr s.unop.property) (fun i _ ↦ hU i)

end FrobeniusSplitting
