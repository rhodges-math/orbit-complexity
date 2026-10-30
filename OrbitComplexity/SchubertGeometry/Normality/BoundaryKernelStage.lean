import OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryFieldKernels

/-! # A coefficient stage for boundary image ideals

The finite affine cover is selected from the prescribed arithmetic target.
The resulting stage preserves its image ideal on every field fibre, and may
be chosen above any finitely generated coefficient ring.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry

universe u

/-- Boundary image ideals persist on field fibres after enlarging coefficients;
the affine covers and their section comparisons are constructed internally. -/
theorem exists_boundary_kernel_stage {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D : Over (Spec (.of S))) (X Y : Over (Spec (.of K)))
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [CompactSpace D.left]
    (e : C ⟶ D) (f : X ⟶ Y)
    [QuasiCompact e.left] [QuasiCompact f.left] [Surjective f.left] [IsReduced Y.left]
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qC ≫ e.left = f.left ≫ qD)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ start ≤ R ∧ ∃ hSR : S ≤ R,
      ∀ (L : Type u) [Field L] [Algebra R L]
        (XL YL : Over (Spec (.of L))) (fL : XL ⟶ YL) [QuasiCompact fL.left]
        (qXL : XL.left ⟶ C.left) (qYL : YL.left ⟶ D.left)
        (_hXL : IsPullback qXL XL.hom C.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))))
        (_hYL : IsPullback qYL YL.hom D.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))))
        (_hfL : fL.left ≫ qYL = qXL ≫ e.left),
        IsSchemeTheoreticallyDominant fL.left ∧
          ∀ (Z : Scheme.{u}) (j : YL.left ⟶ Z), (fL.left ≫ j).ker = j.ker := by
  let V := D.left.affineCover.finiteSubcover
  let W : V.I₀ → D.left.Opens := fun i ↦ (V.f i).opensRange
  have hW (i : V.I₀) : IsAffineOpen (W i) := isAffineOpen_opensRange (V.f i)
  exact exists_boundary_field_kernels S hS C D X Y e f qC qD hC hD hsquare
    W hW V.iSup_opensRange start hstart

end SchubertGeometry
