import OrbitComplexity.SchubertGeometry.Normality.TransverseReduced
import OrbitComplexity.GroupActions.Varieties.Reduced.ClosedKernels
import OrbitComplexity.FrobeniusSplitting.Normality.Images.ClosedIntersectionKernel
import OrbitComplexity.SchubertGeometry.Cells.Richardson

/-! The Richardson ideal and the scheme-theoretic intersection ideal. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SchubertGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The Richardson variety and the scheme-theoretic intersection have
identical ideal sheaves in the flag variety. -/
theorem richardson_intersection_ker (v w : G.weylGroup) :
    (richardsonInclusion G v w).left.ker =
      (pullback.fst (schubertInclusion G w).left (oppositeSchubertInclusion G v).left ≫
        (schubertInclusion G w).left).ker := by
  have : IsReduced (pullback (schubertInclusion G w).left
      (oppositeSchubertInclusion G v).left) := by
    let c := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K)))
      (schubertInclusion G w) (oppositeSchubertInclusion G v)
    exact @isReduced_of_isOpenImmersion _ _ c.inv inferInstance
      (schubert_intersection_reduced G v w)
  have : IsReduced (richardsonVariety G v w).toOver.left := by
    change IsReduced (richardsonVariety G v w).scheme
    infer_instance
  apply GroupActions.closed_ker_eq_of_reduced_range
  rw [Scheme.Pullback.range_fst_comp, richardsonInclusion_range]

/-- The defining ideal sheaf of the Richardson variety is the sum of
its two Schubert ideal sheaves. -/
theorem richardson_ker_eq_sup (v w : G.weylGroup) :
    (richardsonInclusion G v w).left.ker =
      (schubertInclusion G w).left.ker ⊔ (oppositeSchubertInclusion G v).left.ker := by
  exact (richardson_intersection_ker G v w).trans
    (FrobeniusSplitting.closed_intersection_ker
      (schubertInclusion G w).left (oppositeSchubertInclusion G v).left)

/-- On each original affine flag chart, the Richardson quotient has the sum of
the two original Schubert quotient kernels. -/
theorem richardson_app_ker (v w : G.weylGroup)
    (U : (flagVariety G).scheme.affineOpens) :
    RingHom.ker ((richardsonInclusion G v w).left.app U.1).hom =
      RingHom.ker ((schubertInclusion G w).left.app U.1).hom ⊔
        RingHom.ker ((oppositeSchubertInclusion G v).left.app U.1).hom := by
  have h := congrArg (fun J : (flagVariety G).scheme.IdealSheafData => J.ideal U)
    (richardson_ker_eq_sup G v w)
  simpa only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_sup, Pi.sup_apply] using h

end SchubertGeometry
