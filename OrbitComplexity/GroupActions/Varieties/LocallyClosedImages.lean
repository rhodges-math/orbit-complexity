import OrbitComplexity.GroupActions.Varieties.Dimension
import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.GroupActions.Varieties.ClosedPoints

/-! # Local closedness of morphism images

For morphisms of varieties over an algebraically closed field, local closedness of the image
on rational points implies local closedness of the scheme image. Constructibility and the
Jacobson property make it enough to compare closed points.

## Main results

* `GroupActions.Variety.isLocallyClosed_range`: rational-point local closedness detects local
  closedness of a variety morphism's image.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : GroupActions.Variety K}

/-- Local closedness of a variety morphism's image can be checked on rational points. -/
theorem isLocallyClosed_range (f : X.toOver ⟶ Y.toOver)
    (hpoints : IsLocallyClosed (Set.range (mapPoints f))) :
    IsLocallyClosed (Set.range (f.left : X.scheme → Y.scheme)) := by
  have : JacobsonSpace Y.scheme := LocallyOfFiniteType.jacobsonSpace Y.toSpec
  let S : Set Y.scheme := Set.range (f.left : X.scheme → Y.scheme)
  let O : Set Y.points := Set.range (mapPoints f)
  obtain ⟨W, hW, hOW⟩ := ((isLocallyClosed_tfae O).out 1 5).mp hpoints
  obtain ⟨U, hU, hUW⟩ := Y.isEmbedding_pointMap.isInducing.isOpen_iff.mp hW
  have hclosure : closure O = Y.pointMap ⁻¹' closure S := by
    rw [Y.isEmbedding_pointMap.closure_eq_preimage_closure_image]
    exact congrArg (Set.preimage Y.pointMap) (X.pointClosure_range f)
  have hS : IsConstructible S := isConstructible_range f
  have hUconstruct : IsConstructible U := (NoetherianSpace.isCompact U).isConstructible hU
  have hCconstruct : IsConstructible (closure S) := by
    exact ((NoetherianSpace.isCompact (closure S)ᶜ).isConstructible
      isClosed_closure.isOpen_compl).of_compl
  have heq : S = U ∩ closure S := by
    apply GroupActions.constructible_eq hS (hUconstruct.inter hCconstruct)
    ext p
    constructor
    · rintro ⟨hp, hpc⟩
      obtain ⟨y, hy⟩ := Y.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
      have hyeval : Y.pointMap y = p := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := exists_mapPoints_eq f y (hyeval.symm ▸ hp)
      have hyO : y ∈ O := ⟨x, hx⟩
      rw [hOW, ← hUW, hclosure] at hyO
      exact ⟨⟨hyeval ▸ hyO.1, hyeval ▸ hyO.2⟩, hpc⟩
    · rintro ⟨hp, hpc⟩
      obtain ⟨y, hy⟩ := Y.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
      have hyeval : Y.pointMap y = p := congrArg Subtype.val hy
      have hyO : y ∈ O := by
        rw [hOW, ← hUW, hclosure]
        change Y.pointMap y ∈ U ∧ Y.pointMap y ∈ closure S
        rw [hyeval]
        exact hp
      obtain ⟨x, hx⟩ := hyO
      refine ⟨⟨X.pointMap x, ?_⟩, hpc⟩
      exact (pointMap_mapPoints f x).symm.trans ((congrArg Y.pointMap hx).trans hyeval)
  exact ⟨U, closure S, hU, isClosed_closure, heq⟩

end GroupActions.Variety
