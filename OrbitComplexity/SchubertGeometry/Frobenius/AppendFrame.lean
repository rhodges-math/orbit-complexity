import OrbitComplexity.SchubertGeometry.BSDH.EndpointCharts
import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.SchubertGeometry.Normality.Models.RankoneSections

/-! # The rightmost simple frame in the chosen BSDH append chart

The chart c is the SAME product chart and its endpoint equation is the one
constructed by bsdh_append_chart_endpoint. Restricting its newest factor to
the positive chart gives the quotient of the original prior group frame times
x_i(T)n_i inverse, in that order. No polynomial normalization is assumed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u

namespace SchubertGeometry

private theorem orbit_comp {K : Type u} [Field K]
    (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    {Z : Over (Spec (.of K))} (h : Z ⟶ H.toOver) (x : X.points) :
    h ≫ Variety.orbitMorphism H X x = h • (toUnit Z ≫ X.pointsEquivOverHom x) := by
  simp only [Variety.orbitMorphism, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc, CategoryTheory.Hom.smul_def]

private theorem quotient_orbit {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) :
    flagQuotientMorphism G = Variety.orbitMorphism (reductiveVariety G) (flagVariety G)
      (flagVarietyPointsEquiv G (baseFlag G)) := by
  symm
  apply Variety.mapPoints_injective
  funext p
  obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective p
  rw [Variety.mapPoints_orbitMorphism, flagVarietyAction_points]
  change flagVarietyPointsEquiv G (g • baseFlag G) =
    Variety.mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G g)
  rw [flagQuotientMorphism_points]
  apply congrArg (flagVarietyPointsEquiv G)
  change flagProjection G (g * 1) = flagProjection G g
  rw [mul_one]

private theorem quotient_mul {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {Z : Over (Spec (.of K))}
    (r s : Z ⟶ (reductiveVariety G).toOver) :
    (r * s) ≫ flagQuotientMorphism G = r • (s ≫ flagQuotientMorphism G) := by
  rw [quotient_orbit, orbit_comp, orbit_comp, mul_smul]

/-- The positive part of the SAME chosen append chart has endpoint equal to
its original prior group lift multiplied on the RIGHT by the simple
frame x_i(T)n_i inverse, followed by the flag quotient. The sole chart equation
is the bundle-endpoint equation produced by bsdh_append_chart_endpoint. -/
theorem appendPositiveFrame_endpoint {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) (U : Over (Spec (.of K)))
    (g : G.points) (a : U ⟶ (oppositeUnipotentVariety G).toOver)
    (c : U ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ g) :
    ((𝟙 U ⊗ₘ simplePositiveChart G i) ≫ c).left ≫ bsdhMap G (word ++ [i]) =
      (((fst U (additiveVariety K).toOver ≫ a ≫ flagChartMap G g) *
        (snd U (additiveVariety K).toOver ≫ simplePositiveSection G i)) ≫
          flagQuotientMorphism G).left := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let A := (additiveVariety K).toOver
  let j := schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let k := 𝟙 U ⊗ₘ simplePositiveChart G i
  let action : (oppositeUnipotentVariety G).toOver ⊗ Y.toOver ⟶ (flagVariety G).toOver :=
    (fst (oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMap G g) •
      (snd (oppositeUnipotentVariety G).toOver Y.toOver ≫ j)
  have he : (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G Y) ≫
        flagBundleMap G Y j = bsdhMap G (word ++ [i]) :=
    bsdhAppendIso_endpoint G word i
  have hc : c.left ≫ bsdhMap G (word ++ [i]) =
      (a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g ≫ flagBundleMap G Y j := by
    calc
      _ = c.left ≫ ((bsdhAppendIso G word i).hom.left ≫
          pullback.snd (bsdhMap G word) (flagBundleProjection G Y) ≫
            flagBundleMap G Y j) := congrArg (fun f ↦ c.left ≫ f) he.symm
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ flagBundleMap G Y j) hend
  have hh := congrArg (fun f ↦ k.left ≫ f) hc
  have hact : k ≫ (a ⊗ₘ 𝟙 Y.toOver) ≫ action =
      ((fst U A ≫ a ≫ flagChartMap G g) *
        (snd U A ≫ simplePositiveSection G i)) ≫ flagQuotientMorphism G := by
    dsimp only [k, action, A, Y, j]
    simp only [ModObj.comp_smul, tensorHom_fst_assoc, tensorHom_snd_assoc,
      Category.id_comp]
    rw [← simplePositiveSection_quotient]
    exact (quotient_mul G (fst U A ≫ a ≫ flagChartMap G g)
      (snd U A ≫ simplePositiveSection G i)).symm
  calc
    _ = k.left ≫ (a ⊗ₘ 𝟙 Y.toOver).left ≫
        flagBundleChart G Y g ≫ flagBundleMap G Y j := by
      simpa only [k, Over.comp_left, Category.assoc] using hh
    _ = (k ≫ (a ⊗ₘ 𝟙 Y.toOver) ≫ action).left := by
      rw [flagBundleChart_map]
      rfl
    _ = _ := congrArg Over.Hom.left hact

end SchubertGeometry
