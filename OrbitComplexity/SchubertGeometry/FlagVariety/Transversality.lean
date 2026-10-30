import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorCharts
import OrbitComplexity.SchubertGeometry.FlagVariety.BorelProduct
import OrbitComplexity.SchubertGeometry.Cells.Opposite
import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.GroupActions.Actions.Intersections

/-! # Smooth transverse action families on the flag variety

Local Borel torsor charts give a smooth quotient map. They also provide local
coordinates for the paired action on two copies of the flag variety.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace SchubertGeometry
noncomputable section
universe u v w

section Categorical
variable {C : Type w} [Category.{v} C] [CartesianMonoidalCategory C]

private def rightShear (H A : C) [GrpObj H] (s : A ⟶ H) : H ⊗ A ≅ H ⊗ A where
  hom := lift (fst H A * (snd H A ≫ s)) (snd H A)
  inv := lift (fst H A * (snd H A ≫ s)⁻¹) (snd H A)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, mul_assoc]

private def actionShear (H O X : C) [GrpObj O] [ModObj O X] (s : H ⟶ O) :
    H ⊗ X ≅ H ⊗ X where
  hom := lift (fst H X) ((fst H X ≫ s) • snd H X)
  inv := lift (fst H X) ((fst H X ≫ s)⁻¹ • snd H X)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [ModObj.comp_smul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ModObj.comp_smul]

private theorem tensor_snd_pullback (H : C) {U X : C} (j : U ⟶ X) :
    IsPullback (H ◁ j) (snd H U) (snd H X) j := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift (s.fst ≫ fst H X) s.snd
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using s.condition.symm
  · intro s
    simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun t => t ≫ fst H X) h1
      simpa using h
    · simpa using h2

private def actionPairChart (H X : C) [MonObj H] [ModObj H X] {U : C} (j : U ⟶ X) :
    H ⊗ U ⟶ X ⊗ U :=
  lift (fst H U • (snd H U ≫ j)) (snd H U)

private theorem actionPairChart_pullback (H X : C) [MonObj H] [ModObj H X]
    {U : C} (j : U ⟶ X) :
    IsPullback (H ◁ j) (actionPairChart H X j) (ModObj.leftSMul H X) (X ◁ j) := by
  apply IsPullback.of_bot (v₂₁ := snd X U) (v₂₂ := snd X X) (h₃₁ := j)
      ?_ ?_ (tensor_snd_pullback X j)
  · simpa only [actionPairChart, lift_snd, ModObj.leftSMul_snd] using
      tensor_snd_pullback H j
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, ModObj.leftSMul_fst, actionPairChart,
        whiskerLeft_fst, lift_fst, Hom.smul_def]
      apply congrArg (fun t : H ⊗ U ⟶ H ⊗ X => t ≫ γ[H, X])
      apply CartesianMonoidalCategory.hom_ext <;> simp
    · simp [actionPairChart, ModObj.leftSMul]

private theorem restricted_smul (H M X : C) [MonObj H] [MonObj M] [ModObj M X]
    (j : H ⟶ M) [IsMonHom j] {T : C} (h : T ⟶ H) (x : T ⟶ X) :
    letI := Mod.scalarRestriction j X
    h • x = (h ≫ j) • x := by
  change lift h x ≫ (j ▷ X) ≫ γ[M, X] = _
  rw [lift_whiskerRight_assoc]
  rfl

end Categorical

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem bigCellFst_smooth : Smooth (bigCellFst G).left := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  change Smooth (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : G.oppositeUnipotentAlgebra →ₐ[K]
      G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra).toRingHom))
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The flag quotient is smooth, as seen on its Borel torsor charts. -/
theorem flagQuotientMorphism_smooth : Smooth (flagQuotientMorphism G).left := by
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Smooth.{u})
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth.{u}) (flagSchemeCover G)
  intro g
  change G.points at g
  change Smooth (pullback.snd (flagQuotientMorphism G).left (flagChartMorphism G g).left)
  have h : IsPullback (bigCellFst G).left (translatedBigCell G g).left
      (flagChartMorphism G g).left (flagQuotientMorphism G).left :=
    (flagTorsorPullback G g).map (Over.forget (Spec (CommRingCat.of K)))
  have : Smooth (bigCellFst G).left := bigCellFst_smooth G
  rw [← h.flip.isoPullback_inv_snd]
  infer_instance

private theorem quotient_orbit : flagQuotientMorphism G =
    Variety.orbitMorphism (reductiveVariety G) (flagVariety G)
      (flagVarietyPointsEquiv G (baseFlag G)) := by
  apply Variety.mapPoints_injective
  funext q
  obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective q
  change Variety.mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G g) = _
  rw [flagQuotientMorphism_points, Variety.mapPoints_orbitMorphism,
    flagVarietyAction_points]
  change flagVarietyPointsEquiv G (flagProjection G g) =
    flagVarietyPointsEquiv G (flagProjection G (g * 1))
  rw [mul_one]

private theorem quotient_mul {T : Over (Spec (CommRingCat.of K))}
    (a b : T ⟶ (reductiveVariety G).toOver) :
    (a * b) ≫ flagQuotientMorphism G = a • (b ≫ flagQuotientMorphism G) := by
  rw [quotient_orbit]
  change (a * b) ≫ (𝟙 (reductiveVariety G).toOver •
      (toUnit (reductiveVariety G).toOver ≫
        (flagVariety G).pointsEquivOverHom (flagVarietyPointsEquiv G (baseFlag G)))) = _
  change _ = a • (b ≫ (𝟙 (reductiveVariety G).toOver •
      (toUnit (reductiveVariety G).toOver ≫
        (flagVariety G).pointsEquivOverHom (flagVarietyPointsEquiv G (baseFlag G)))))
  simp only [ModObj.comp_smul, Category.comp_id, comp_toUnit_assoc, mul_smul]

private theorem actionPairChart_eq (g : G.points) :
    actionPairChart (reductiveVariety G).toOver (flagVariety G).toOver
        (flagChartMorphism G g) =
      (rightShear (reductiveVariety G).toOver (oppositeUnipotentVariety G).toOver
        (flagChartMap G g)).hom ≫
          (flagQuotientMorphism G ⊗ₘ 𝟙 (oppositeUnipotentVariety G).toOver) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [actionPairChart, lift_fst, Category.assoc, tensorHom_fst,
      rightShear, lift_fst_assoc]
    rw [quotient_mul, Category.assoc, flagChartMap_quotient]
  · simp [actionPairChart, rightShear]

private theorem actionPairChart_smooth (g : G.points) :
    Smooth (actionPairChart (reductiveVariety G).toOver (flagVariety G).toOver
      (flagChartMorphism G g)).left := by
  have : Smooth (flagQuotientMorphism G).left := flagQuotientMorphism_smooth G
  have hid : Smooth
      (𝟙 _ : (oppositeUnipotentVariety G).toOver ⟶
        (oppositeUnipotentVariety G).toOver).left := by
    change Smooth (𝟙 (oppositeUnipotentVariety G).scheme)
    infer_instance
  have ht : Smooth
      (flagQuotientMorphism G ⊗ₘ 𝟙 (oppositeUnipotentVariety G).toOver).left :=
    MorphismProperty.pullbackMap (P := @Smooth) (by infer_instance)
      hid (flagQuotientMorphism G).w.symm (by simp)
  rw [actionPairChart_eq]
  change Smooth (_ ≫ (flagQuotientMorphism G ⊗ₘ
    𝟙 (oppositeUnipotentVariety G).toOver).left)
  infer_instance

private instance flagProductChart_open (g : G.points) :
    IsOpenImmersion ((flagVariety G).toOver ◁ flagChartMorphism G g).left := by
  have h : IsPullback ((flagVariety G).toOver ◁ flagChartMorphism G g).left
      (snd (flagVariety G).toOver (oppositeUnipotentVariety G).toOver).left
      (snd (flagVariety G).toOver (flagVariety G).toOver).left
      (flagChartMorphism G g).left :=
    (tensor_snd_pullback (flagVariety G).toOver (flagChartMorphism G g)).map
      (Over.forget (Spec (CommRingCat.of K)))
  exact MorphismProperty.of_isPullback h.flip inferInstance

private def flagPairCover : Scheme.OpenCover
    ((flagVariety G).toOver ⊗ (flagVariety G).toOver).left where
  I₀ := G.points
  X _ := ((flagVariety G).toOver ⊗ (oppositeUnipotentVariety G).toOver).left
  f g := ((flagVariety G).toOver ◁ flagChartMorphism G g).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro z
      obtain ⟨g, p, hp⟩ := (flagSchemeCover G).exists_eq
        ((snd (flagVariety G).toOver (flagVariety G).toOver).left z)
      change (flagChartMorphism G g).left p =
        (snd (flagVariety G).toOver (flagVariety G).toOver).left z at hp
      have h := (tensor_snd_pullback (flagVariety G).toOver (flagChartMorphism G g)).map
        (Over.forget (Spec (CommRingCat.of K)))
      have hz : z ∈ Set.range (pullback.fst
          (snd (flagVariety G).toOver (flagVariety G).toOver).left
          (flagChartMorphism G g).left) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hz
      exact ⟨g, h.isoPullback.inv q,
        (congrArg (fun t => t q) h.isoPullback_inv_fst).trans hq⟩
    · infer_instance

private theorem flagActionPair_smooth : Smooth
    (ModObj.leftSMul (reductiveVariety G).toOver (flagVariety G).toOver).left := by
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Smooth.{u})
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth.{u}) (flagPairCover G)
  intro g
  change G.points at g
  change Smooth (pullback.snd
    (ModObj.leftSMul (reductiveVariety G).toOver (flagVariety G).toOver).left
    ((flagVariety G).toOver ◁ flagChartMorphism G g).left)
  have h : IsPullback ((reductiveVariety G).toOver ◁ flagChartMorphism G g).left
      (actionPairChart (reductiveVariety G).toOver (flagVariety G).toOver
        (flagChartMorphism G g)).left
      (ModObj.leftSMul (reductiveVariety G).toOver (flagVariety G).toOver).left
      ((flagVariety G).toOver ◁ flagChartMorphism G g).left :=
    (actionPairChart_pullback (reductiveVariety G).toOver (flagVariety G).toOver
      (flagChartMorphism G g)).map (Over.forget (Spec (CommRingCat.of K)))
  have : Smooth (actionPairChart (reductiveVariety G).toOver (flagVariety G).toOver
    (flagChartMorphism G g)).left := actionPairChart_smooth G g
  rw [← h.isoPullback_inv_snd]
  infer_instance

private def inverseBorelMul :
    (borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver ⟶
      (reductiveVariety G).toOver :=
  (𝟙 (borelVariety G).toOver ⊗ₘ ι[(oppositeBorelVariety G).toOver]) ≫
    borelOppositeMul G

private theorem inverseBorelMul_pair {T : Over (Spec (CommRingCat.of K))}
    (h : T ⟶ (borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver) :
    h ≫ inverseBorelMul G =
      (h ≫ fst _ _ ≫ borelInclusion G) *
        (h ≫ snd _ _ ≫ oppositeBorelInclusion G)⁻¹ := by
  have he : h ≫ (𝟙 (borelVariety G).toOver ⊗ₘ
        ι[(oppositeBorelVariety G).toOver]) =
      lift (h ≫ fst _ _) (h ≫ snd _ _)⁻¹ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Hom.inv_def]
  rw [inverseBorelMul, ← Category.assoc, he, borelOppositeMul_pair, GrpObj.inv_comp]
  simp only [Category.assoc]

private theorem inverseBorelMul_smooth : Smooth (inverseBorelMul G).left := by
  change Smooth (_ ≫ (borelOppositeMul G).left)
  infer_instance

private theorem transverseAction_factor :
    let B := (borelVariety G).toOver
    let O := (oppositeBorelVariety G).toOver
    let F := (flagVariety G).toOver
    transverseAction B O F =
      (actionShear (B ⊗ O) O F (snd B O)).hom ≫
        (inverseBorelMul G ▷ F) ≫
          ModObj.leftSMul (reductiveVariety G).toOver F := by
  dsimp only
  rw [actionShear, lift_whiskerRight_assoc, ModObj.lift_leftSMul]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transverseAction, lift_fst]
    rw [inverseBorelMul_pair]
    rw [restricted_smul (borelVariety G).toOver (reductiveVariety G).toOver
      (flagVariety G).toOver (borelInclusion G)]
    rw [restricted_smul (oppositeBorelVariety G).toOver (reductiveVariety G).toOver
      (flagVariety G).toOver (oppositeBorelInclusion G)]
    simp only [Category.assoc, mul_smul, inv_smul_smul]
  · simp only [transverseAction, lift_snd]

/-- The independent Borel and opposite-Borel actions form a smooth paired flag map. -/
theorem flagTransverseAction_smooth : Smooth
    (transverseAction (borelVariety G).toOver (oppositeBorelVariety G).toOver
      (flagVariety G).toOver).left := by
  have : Smooth (inverseBorelMul G).left := inverseBorelMul_smooth G
  have hid : Smooth (𝟙 _ : (flagVariety G).toOver ⟶ (flagVariety G).toOver).left := by
    change Smooth (𝟙 (flagVariety G).scheme)
    infer_instance
  have ht : Smooth (inverseBorelMul G ▷ (flagVariety G).toOver).left :=
    MorphismProperty.pullbackMap (P := @Smooth) (by infer_instance) hid
      (inverseBorelMul G).w.symm (by simp)
  have : Smooth
      (ModObj.leftSMul (reductiveVariety G).toOver (flagVariety G).toOver).left :=
    flagActionPair_smooth G
  rw [transverseAction_factor]
  change Smooth (_ ≫ _ ≫ _)
  infer_instance

end
end SchubertGeometry
