import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveMatrices
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveFlags
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveCharts
import OrbitComplexity.GroupActions.Varieties.AdditiveOpens
import OrbitComplexity.GroupActions.Varieties.CoordinateInversion

/-! # The Laurent overlap of arbitrary-root charts

The matrix identity is first passed through the rank-one point homomorphism. Upper and
diagonal stabilizers give the flag identity. Rational-point detection is then used only
on the reduced punctured affine line, producing an equality of scheme morphisms which
can be precomposed with maps from arbitrary, possibly nonreduced, schemes.
-/

noncomputable section

namespace SchubertGeometry

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
open scoped Matrix

universe u

private theorem sl2_overlap {K : Type u} [Field K] (t : Kˣ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (t : K) =
      Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1)
          ((t⁻¹ : Kˣ) : K) * sl2Weyl K *
        Matrix.SpecialLinearGroup.diag2 (t : K) t.ne_zero *
          Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1)
            ((t⁻¹ : Kˣ) : K) := by
  apply Subtype.ext
  change Matrix.transvection (1 : Fin 2) 0 (t : K) =
    Matrix.transvection (0 : Fin 2) 1 ((t⁻¹ : Kˣ) : K) *
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
        (Matrix.SpecialLinearGroup.diag2 (t : K) t.ne_zero).val *
          Matrix.transvection (0 : Fin 2) 1 ((t⁻¹ : Kˣ) : K)
  rw [Matrix.SpecialLinearGroup.diag2_coe']
  have hl : Matrix.transvection (1 : Fin 2) 0 (t : K) = !![1, 0; (t : K), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]
  have hu : Matrix.transvection (0 : Fin 2) 1 ((t⁻¹ : Kˣ) : K) =
      !![1, ((t⁻¹ : Kˣ) : K); 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]
  rw [hl, hu]
  simpa only [Units.val_inv_eq_inv_val] using rootCurve_matrix_overlap t

private theorem over_precomp {C : Type*} [Category C] {B : C}
    {U V W Y Z : Over B} {a : U ⟶ V} {b : V ⟶ Z}
    {c : U ⟶ W} {d : W ⟶ Y} {e : Y ⟶ Z}
    (he : a ≫ b = c ≫ d ≫ e) {S : C} (g : S ⟶ U.left) :
    g ≫ a.left ≫ b.left = g ≫ c.left ≫ d.left ≫ e.left := by
  have hh := congrArg Over.Hom.left he
  simpa only [Over.comp_left, Category.assoc] using congrArg (fun f => g ≫ f) hh

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The lower and upper root parameters give the same flag on their unit overlap. -/
theorem rootCurve_flag_overlap (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (t : Kˣ) :
    gaParameterPoint (rootLowerMap G w i) (t : K) •
        flagProjection G (G.weylPoint x) =
      gaParameterPoint (rootUpperMap G w i) ((t⁻¹ : Kˣ) : K) •
        flagProjection G (G.weylPoint
          (RootPairing.weylGroup.ofIdx G.rootSystem
            (G.rootSystem.weylGroupToPerm w i.val) * x)) := by
  have hf := congrArg (rootSl2Points G w i) (sl2_overlap t)
  simp only [map_mul, rootSl2Points_upper, rootSl2Points_lower] at hf
  calc
    gaParameterPoint (rootLowerMap G w i) (t : K) •
        flagProjection G (G.weylPoint x) =
      gaParameterPoint (rootUpperMap G w i) ((t⁻¹ : Kˣ) : K) •
        (rootSl2Points G w i (sl2Weyl K) • flagProjection G (G.weylPoint x)) := by
      exact rootCurve_action_factor _ _ _ _ _ hf
        (rootUpperMap_fixes G w i x hpos _) (rootSl2Points_diagonal_fixes G w i t x)
    _ = _ := by rw [rootSl2Points_weyl_flag]

/-- The two root parameters have reciprocal nonzero field parameters on their common chart. -/
theorem rootCurve_flag_transition (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) {t : K} (ht : t ≠ 0) :
    gaParameterPoint (rootLowerMap G w i) t • flagProjection G (G.weylPoint x) =
      gaParameterPoint (rootUpperMap G w i) t⁻¹ •
        flagProjection G (G.weylPoint
          (RootPairing.weylGroup.ofIdx G.rootSystem
            (G.rootSystem.weylGroupToPerm w i.val) * x)) := by
  simpa only [Units.val_mk0, Units.val_inv_eq_inv_val] using
    rootCurve_flag_overlap G w i x hpos (Units.mk0 t ht)

/-- The zero chart has its specified lower-root orbit formula on rational points. -/
theorem rootCurve_zeroChart_points (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (t : K) :
    Variety.mapPoints (rootCurveZeroChart G w i x) (additivePointsEquiv K t) =
      flagVarietyPointsEquiv G
        (gaParameterPoint (rootLowerMap G w i) t • flagProjection G (G.weylPoint x)) := by
  rw [rootCurveZeroChart, Variety.mapPoints_comp, gaMorphism_points,
    Variety.mapPoints_orbitMorphism]
  change reductivePointsMulEquiv G (gaParameterPoint (rootLowerMap G w i) t) •
    flagVarietyPointsEquiv G (flagProjection G (G.weylPoint x)) = _
  exact flagVarietyAction_points G _ _

/-- The infinity chart has its specified upper-root orbit formula on rational points. -/
theorem rootCurve_infinityChart_points (w : G.weylGroup) (i : G.rootBase.support)
    (y : G.weylGroup) (t : K) :
    Variety.mapPoints (rootCurveInfinityChart G w i y) (additivePointsEquiv K t) =
      flagVarietyPointsEquiv G
        (gaParameterPoint (rootUpperMap G w i) t • flagProjection G (G.weylPoint y)) := by
  rw [rootCurveInfinityChart, Variety.mapPoints_comp, gaMorphism_points,
    Variety.mapPoints_orbitMorphism]
  change reductivePointsMulEquiv G (gaParameterPoint (rootUpperMap G w i) t) •
    flagVarietyPointsEquiv G (flagProjection G (G.weylPoint y)) = _
  exact flagVarietyAction_points G _ _

/-- The root charts agree on all rational points of the punctured line after inversion. -/
theorem rootCurve_charts_transition (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) {t : K} (ht : t ≠ 0) :
    Variety.mapPoints (rootCurveZeroChart G w i x) (additivePointsEquiv K t) =
      Variety.mapPoints (rootCurveInfinityChart G w i
        (RootPairing.weylGroup.ofIdx G.rootSystem
          (G.rootSystem.weylGroupToPerm w i.val) * x)) (additivePointsEquiv K t⁻¹) := by
  rw [rootCurve_zeroChart_points, rootCurve_infinityChart_points]
  exact congrArg (flagVarietyPointsEquiv G) (rootCurve_flag_transition G w i x hpos ht)

/-- The specified two root-chart morphisms agree on the reduced Laurent overlap. -/
theorem rootCurve_overlap_comp (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    (additiveVariety K).openInclusion (additiveNonzero K) ≫ rootCurveZeroChart G w i x =
      (puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K) ≫
          rootCurveInfinityChart G w i
            (RootPairing.weylGroup.ofIdx G.rootSystem
              (G.rootSystem.weylGroupToPerm w i.val) * x) := by
  apply Variety.mapPoints_injective
  funext p
  let t := (additivePointsEquiv K).symm (Variety.mapPoints
    ((additiveVariety K).openInclusion (additiveNonzero K)) p)
  have ht : t ≠ 0 := by
    change Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) p ∈
      {x | (additivePointsEquiv K).symm x ≠ 0}
    rw [← additiveNonzero_points K]
    exact ⟨p, rfl⟩
  have hp0 : Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) p =
      additivePointsEquiv K t := (Equiv.apply_symm_apply _ _).symm
  have hp1 : Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K))
      (Variety.mapPoints (puncturedAdditiveInvIso K).hom p) =
        additivePointsEquiv K t⁻¹ := by
    apply (additivePointsEquiv K).symm.injective
    rw [Equiv.symm_apply_apply]
    exact puncturedAdditiveInvIso_points K p
  simp only [Variety.mapPoints_comp]
  rw [hp0, hp1]
  exact rootCurve_charts_transition G w i x hpos ht

/-- The Laurent-overlap identity can be tested on any scheme, without a reducedness hypothesis. -/
theorem rootCurve_overlap_precomp (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) {S : Scheme}
    (g : S ⟶ ((additiveVariety K).openSubvariety (additiveNonzero K)).scheme) :
    g ≫ ((additiveVariety K).openInclusion (additiveNonzero K)).left ≫
        (rootCurveZeroChart G w i x).left =
      g ≫ (puncturedAdditiveInvIso K).hom.left ≫
        ((additiveVariety K).openInclusion (additiveNonzero K)).left ≫
          (rootCurveInfinityChart G w i
            (RootPairing.weylGroup.ofIdx G.rootSystem
              (G.rootSystem.weylGroupToPerm w i.val) * x)).left := by
  exact over_precomp (rootCurve_overlap_comp G w i x hpos) g

-- The global projective-line gluing and endpoint values are defined in RootCurveGluing.
-- RootCurveContainment proves the two scheme-image containments and applies the
-- separately defined Richardson factorization.

end SchubertGeometry
