import OrbitComplexity.SchubertGeometry.ProjectiveLine.PolynomialChart
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveLine
import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorCharts

/-! # Unit sections and the flag-action chart formula -/

noncomputable section
namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

private theorem ga_unit {K : Type u} [Field K] (G : ReductiveGroupData K)
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) :
    η[(additiveVariety K).toOver] ≫ gaMorphism G φ = η[(reductiveVariety G).toOver] := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K
      (SymmetricAlgebra K K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K G.coordinateAlgebra).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  exact congrArg (fun f : G.coordinateAlgebra →ₐ[K] K ↦ CommRingCat.ofHom f.toRingHom)
    (BialgHom.counitAlgHom_comp φ)

private theorem ga_chart_zero {K : Type u} [Field K] (j : ULift.{u} (Fin 2)) :
    η[(additiveVariety K).toOver].left ≫ (projectiveLineChart K j).left =
      projectiveLineSection K j := by
  rw [projectiveLineChart_polynomial]
  change Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K
      (SymmetricAlgebra K K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) ≫
          projectiveLinePolynomialChart K j =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫
      projectiveLinePolynomialChart K j
  rw [← Spec.map_comp_assoc]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp [SymmetricAlgebra.algebraMapInv_ι]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The chart-one zero on the simple projective line maps to the unit flag section. -/
theorem simple_infinity_flag (i : G.rootBase.support) :
    projectiveLineSection K ⟨1⟩ ≫ (simpleSchubertIso G i).inv.left ≫
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left =
      η[(reductiveVariety G).toOver].left ≫ (flagQuotientMorphism G).left := by
  rw [← ga_chart_zero]
  have he : η[(additiveVariety K).toOver] ≫ projectiveLineChart K ⟨1⟩ ≫
        (simpleSchubertIso G i).inv ≫
          schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
      η[(additiveVariety K).toOver] ≫ simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
    rw [← simpleSchubertIso_negative G i]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = (η[(additiveVariety K).toOver] ≫ simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left :=
      congrArg Over.Hom.left he
    _ = _ := by
      rw [simpleNegativeChart_comp, ← Category.assoc, ga_unit]
      rfl

/-- On a unipotent flag chart, the flag action is group multiplication before quotient. -/
theorem flag_action_chart {T : Over (Spec (.of K))}
    (h : T ⟶ (reductiveVariety G).toOver)
    (a : T ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    h • (a ≫ flagChartMorphism G g) =
      (h * (a ≫ flagChartMap G g)) ≫ flagQuotientMorphism G := by
  let b : T ⟶ (flagActionProduct G).toOver := lift h (a ≫ flagChartMorphism G g)
  let v₀ : T.left ⟶ (flagActionChartVariety G g).scheme :=
    pullback.lift b.left a.left (congrArg Over.Hom.left
      (lift_snd h (a ≫ flagChartMorphism G g)))
  have hv₀ : v₀ ≫ (flagActionChartVariety G g).toSpec = T.hom := by
    change v₀ ≫ pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left ≫
      (flagActionProduct G).toSpec = _
    have hf : v₀ ≫ pullback.fst (flagActionSnd G).left
        (flagChartMorphism G g).left = b.left := pullback.lift_fst _ _ _
    rw [← Category.assoc, hf]
    exact b.w
  let v : T ⟶ (flagActionChartVariety G g).toOver := Over.homMk v₀ hv₀
  have hvf : v ≫ flagActionChartFst G g = b := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hvs : v ≫ flagActionChartSnd G g = a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  change b ≫ flagActionMorphism G = _
  calc
    _ = v ≫ flagActionChartFst G g ≫ flagActionMorphism G := by rw [← Category.assoc, hvf]
    _ = v ≫ flagActionChartMorphism G g := by rw [flagActionChart_action]
    _ = _ := by
      change (v ≫ ((flagActionChartFst G g ≫ flagActionFst G) *
        (flagActionChartSnd G g ≫ flagChartMap G g))) ≫ flagQuotientMorphism G = _
      rw [MonObj.comp_mul, ← Category.assoc v (flagActionChartFst G g), hvf,
        ← Category.assoc v (flagActionChartSnd G g), hvs]
      simp only [b, flagActionFst, lift_fst]

end SchubertGeometry
