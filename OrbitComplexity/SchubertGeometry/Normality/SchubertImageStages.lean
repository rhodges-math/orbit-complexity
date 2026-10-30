import OrbitComplexity.SchubertGeometry.Normality.BoundaryKernelStage
import OrbitComplexity.SchubertGeometry.BSDH.Surjectivity
import OrbitComplexity.SchubertGeometry.BSDH.Opposite

/-! # Image-ideal stages for Schubert endpoints

Reduced-word endpoints to ordinary and opposite Schubert varieties give
coefficient stages on which all field endpoints retain the ambient image ideal.
The comparison uses surjectivity and reducedness over the coefficient field;
no reducedness of the specialized Schubert model is needed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups

namespace SchubertGeometry

universe u

private theorem variety_over_reduced {K : Type u} [Field K]
    (V : GroupActions.Variety K) : IsReduced V.toOver.left := V.reduced

/-- A model of a reduced-word Schubert endpoint retains its image ideal on
every field fibre after a coefficient extension above the chosen start. -/
theorem exists_schubert_kernel_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D : Over (Spec (.of S)))
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [CompactSpace D.left] (e : C ⟶ D) [QuasiCompact e.left]
    (qC : (bsdhVariety G word).toOver.left ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase word)).toOver.left ⟶ D.left)
    (hC : IsPullback qC (bsdhVariety G word).toOver.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD
      (schubertVariety G (simpleWeylWord G.rootBase word)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qC ≫ e.left = (bsdhSchubertMap G word hred).left ≫ qD)
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
  let : IsReduced
      (schubertVariety G (simpleWeylWord G.rootBase word)).toOver.left :=
    variety_over_reduced _
  exact exists_boundary_kernel_stage S hS C D _ _ e
    (bsdhSchubertMap G word hred) qC qD hC hD hsquare start hstart

/-- A model of the opposite reduced-word endpoint retains its image ideal on
every field fibre after a coefficient extension above the chosen start. -/
theorem exists_opposite_kernel_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D : Over (Spec (.of S)))
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [CompactSpace D.left] (e : C ⟶ D) [QuasiCompact e.left]
    (qC : (bsdhVariety G word).toOver.left ⟶ C.left)
    (qD : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left ⟶ D.left)
    (hC : IsPullback qC (bsdhVariety G word).toOver.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qC ≫ e.left = (bsdhOppositeSchubertMap G word hred).left ≫ qD)
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
  let : IsReduced (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left :=
    variety_over_reduced _
  let : GeometricallyConnected (bsdhOppositeSchubertMap G word hred).left :=
    bsdhOppositeSchubert_geomConnected G word hred
  exact exists_boundary_kernel_stage S hS C D _ _ e
    (bsdhOppositeSchubertMap G word hred) qC qD hC hD hsquare start hstart

end SchubertGeometry
