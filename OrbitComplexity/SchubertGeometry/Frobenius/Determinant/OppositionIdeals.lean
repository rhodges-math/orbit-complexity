import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionBoundary
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomialChart
import OrbitComplexity.GroupActions.Varieties.Reduced.ClosedKernels
import OrbitComplexity.GroupActions.Varieties.ProductImmersions

/-! # Opposite simple-boundary ideals in transverse coordinates -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonoidalCategory
open GroupActions ReductiveGroups

namespace SchubertGeometry.DeterminantSection

open private chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial

private theorem zero_closed {S : Scheme.{u}} {X Y F : Over S}
    [IsSeparated Y.hom] (y : X ⟶ Y) (e : X ⊗ Y ≅ F) :
    IsClosedImmersion (lift (𝟙 X) y ≫ e.hom).left := by
  have : IsClosedImmersion (lift (𝟙 X) y).left := tensorSection_isClosed X Y y
  change IsClosedImmersion ((lift (𝟙 X) y).left ≫ e.hom.left)
  infer_instance

private theorem chart_kernel {X Y Z D : Scheme.{u}}
    (j : Y ⟶ Z) [IsClosedImmersion j] [IsReduced Y]
    (k : X ⟶ Z) [IsOpenImmersion k]
    (z : D ⟶ X) [IsClosedImmersion z] [IsReduced D]
    (h : k ⁻¹' Set.range j = Set.range z) :
    (Limits.pullback.fst k j).ker = z.ker := by
  let : IsReduced (Limits.pullback k j) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd k j)
  apply closed_ker_eq_of_reduced_range
  exact (Scheme.Pullback.range_fst k j).trans h

private theorem preimage_iso_range {X Y Z B D : Scheme.{u}}
    (e : X ≅ Y) (k : Y ⟶ Z) (j : B ⟶ Z) (z : D ⟶ X) (t : D ⟶ Y)
    (q : X ⟶ Z) (hq : q = e.hom ≫ k)
    (hz : z ≫ e.hom = t) (h : k ⁻¹' Set.range j = Set.range t) :
    q ⁻¹' Set.range j = Set.range z := by
  rw [hq]
  have he (x : X) : e.inv (e.hom x) = x :=
    congrArg (fun f : X ⟶ X => f x) e.hom_inv_id
  ext x
  change e.hom x ∈ k ⁻¹' Set.range j ↔ x ∈ Set.range z
  rw [h]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    have hz' : e.hom (z d) = t d := congrArg (fun f : D ⟶ Y => f d) hz
    exact (he (z d)).symm.trans ((congrArg e.inv (hz'.trans hd)).trans (he x))
  · rintro ⟨d, rfl⟩
    exact ⟨d, (congrArg (fun f : D ⟶ Y => f d) hz).symm⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The zero section of the transverse additive coordinate is a closed immersion. -/
instance oppositionZeroMap_isClosed (i : G.rootBase.support) :
    IsClosedImmersion (oppositionZeroMap G i).left := by
  let : IsSeparated (additiveVariety K).toOver.hom := (additiveVariety K).separated
  exact zero_closed
    (toUnit _ ≫ (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0))
    (oppositeSimpleCoordinates G i)

/-- The opposite simple-boundary ideal pulls back to the zero-section ideal
on its translated transverse chart. -/
theorem oppositionBoundary_kernel (i : G.rootBase.support) :
    (Limits.pullback.fst
      (flagChartMorphism G (oppositionChartPoint G i)).left
      (oppositeSchubertInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left).ker =
      (oppositionZeroMap G i).left.ker := by
  let : IsReduced (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).toOver.left :=
    (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).reduced
  let : IsReduced (rootSubsetVariety G
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))).toOver.left :=
    (rootSubsetVariety G
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))).reduced
  exact chart_kernel
    (oppositeSchubertInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left
    (flagChartMorphism G (oppositionChartPoint G i)).left
    (oppositionZeroMap G i).left (oppositionBoundary_preimage G i)

/-- The polynomial opposition chart pulls the opposite simple-boundary
ideal back to the evaluation-at-zero ideal in that same polynomial ring. -/
theorem oppositionPolynomial_kernel (i : G.rootBase.support) :
    (Limits.pullback.fst (oppositionPolynomialMap G i).left
      (oppositeSchubertInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left).ker =
      (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : chartAlgebra G i)))).ker := by
  have hclosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : chartAlgebra G i)))) :=
    IsClosedImmersion.spec_of_surjective _ (fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩)
  exact @chart_kernel.{u}
    (affineVariety K (Polynomial (chartAlgebra G i))).toOver.left
    (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).toOver.left
    (flagVariety G).toOver.left (Spec (.of (chartAlgebra G i)))
    (oppositeSchubertInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left
    inferInstance
    (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).reduced
    (oppositionPolynomialMap G i).left (oppositionPolynomialMap_open G i)
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : chartAlgebra G i))))
    hclosed inferInstance
    (@preimage_iso_range.{u}
      (affineVariety K (Polynomial (chartAlgebra G i))).toOver.left
      (oppositeUnipotentVariety G).toOver.left (flagVariety G).toOver.left
      (oppositeSchubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).toOver.left
      (Spec (.of (chartAlgebra G i)))
      ((Over.forget (Spec (.of K))).mapIso (oppositionPolynomialIso G i))
      (flagChartMorphism G (oppositionChartPoint G i)).left
      (oppositeSchubertInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : chartAlgebra G i))))
      (oppositionZeroMap G i).left (oppositionPolynomialMap G i).left rfl
      (oppositionPolynomialIso_zero G i) (oppositionBoundary_preimage G i))

end SchubertGeometry.DeterminantSection
