import OrbitComplexity.SchubertGeometry.FlagBundle.Maps
import OrbitComplexity.GroupActions.Actions.RelativeTwist
import OrbitComplexity.GroupActions.Varieties.ProductImmersions

/-! # Closed associated flag correspondences

An equivariant closed inclusion in the flag variety gives a closed two-flag map
from its associated bundle. In a translated flag chart this map is a product
inclusion followed by the action automorphism of the local group section.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (Y : Variety K)
  [ModObj (borelVariety G).toOver Y.toOver]
  (j : Y.toOver ⟶ (flagVariety G).toOver)
  [IsModHom (borelVariety G).toOver j]

private def bundlePair :
    flagBundleScheme G Y ⟶ ((flagVariety G).toOver ⊗ (flagVariety G).toOver).left :=
  pullback.lift (flagBundleProjection G Y) (flagBundleMap G Y j)
    (flagBundleMap_toSpec G Y j).symm

private theorem bundlePair_fst :
    bundlePair G Y j ≫ (fst (flagVariety G).toOver (flagVariety G).toOver).left =
      flagBundleProjection G Y := pullback.lift_fst _ _ _

private theorem bundlePair_snd :
    bundlePair G Y j ≫ (snd (flagVariety G).toOver (flagVariety G).toOver).left =
      flagBundleMap G Y j := pullback.lift_snd _ _ _

private def localPair (g : G.points) :
    (oppositeUnipotentVariety G).toOver ⊗ Y.toOver ⟶
      (oppositeUnipotentVariety G).toOver ⊗ (flagVariety G).toOver :=
  (𝟙 (oppositeUnipotentVariety G).toOver ⊗ₘ j) ≫
    (actionTwist (reductiveVariety G) (oppositeUnipotentVariety G)
      (flagVariety G) (flagChartMap G g)).hom

omit [ModObj (borelVariety G).toOver Y.toOver] [IsModHom (borelVariety G).toOver j] in
private theorem localPair_fst (g : G.points) :
    localPair G Y j g ≫
        fst (oppositeUnipotentVariety G).toOver (flagVariety G).toOver =
      fst (oppositeUnipotentVariety G).toOver Y.toOver := by
  simp only [localPair, Category.assoc, actionTwist_fst, tensorHom_fst, Category.comp_id]

omit [ModObj (borelVariety G).toOver Y.toOver] [IsModHom (borelVariety G).toOver j] in
private theorem localPair_snd (g : G.points) :
    localPair G Y j g ≫
        snd (oppositeUnipotentVariety G).toOver (flagVariety G).toOver =
      (fst (oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMap G g) •
        (snd (oppositeUnipotentVariety G).toOver Y.toOver ≫ j) := by
  simp only [localPair, actionTwist, Category.assoc, lift_snd, ModObj.comp_smul,
    tensorHom_fst_assoc, tensorHom_snd, Category.id_comp]

private theorem bundlePair_chart (g : G.points) :
    flagBundleChart G Y g ≫ bundlePair G Y j =
      (localPair G Y j g ≫ (flagChartMorphism G g ⊗ₘ 𝟙 (flagVariety G).toOver)).left := by
  apply pullback.hom_ext
  · change flagBundleChart G Y g ≫ bundlePair G Y j ≫
      (fst (flagVariety G).toOver (flagVariety G).toOver).left = _
    rw [bundlePair_fst, flagBundleChart_projection]
    change _ = ((localPair G Y j g ≫ (flagChartMorphism G g ⊗ₘ 𝟙 _) ≫ fst _ _).left)
    rw [tensorHom_fst, ← Category.assoc, localPair_fst]
  · change flagBundleChart G Y g ≫ bundlePair G Y j ≫
      (snd (flagVariety G).toOver (flagVariety G).toOver).left = _
    rw [bundlePair_snd, flagBundleChart_map]
    change _ = ((localPair G Y j g ≫ (flagChartMorphism G g ⊗ₘ 𝟙 _) ≫ snd _ _).left)
    rw [tensorHom_snd, Category.comp_id, localPair_snd]

omit [ModObj (borelVariety G).toOver Y.toOver] [IsModHom (borelVariety G).toOver j] in
private theorem localPair_isClosed (g : G.points) [IsClosedImmersion j.left] :
    IsClosedImmersion (localPair G Y j g).left := by
  have : IsClosedImmersion (𝟙 (oppositeUnipotentVariety G).toOver ⊗ₘ j).left := by
    have hpb : IsPullback (snd (oppositeUnipotentVariety G).toOver Y.toOver)
        (𝟙 (oppositeUnipotentVariety G).toOver ⊗ₘ j) j
        (snd (oppositeUnipotentVariety G).toOver (flagVariety G).toOver) := by
      refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
      · intro s
        exact lift (s.snd ≫ fst _ _) s.fst
      · intro s
        simp
      · intro s
        apply CartesianMonoidalCategory.hom_ext
        · simp
        · simpa using s.condition
      · intro s m h1 h2
        apply CartesianMonoidalCategory.hom_ext
        · have he := congrArg (fun t => t ≫ fst _ _) h2
          simpa only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst] using he
        · simpa using h1
    exact MorphismProperty.of_isPullback
      (P := @IsClosedImmersion) (hpb.map (Over.forget _))
      (show IsClosedImmersion j.left from inferInstance)
  have : IsIso (actionTwist (reductiveVariety G) (oppositeUnipotentVariety G)
      (flagVariety G) (flagChartMap G g)).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso
      (actionTwist (reductiveVariety G) (oppositeUnipotentVariety G)
        (flagVariety G) (flagChartMap G g))).hom)
  change IsClosedImmersion (_ ≫ _)
  infer_instance

private theorem tensor_fst_pullback {S : Scheme.{u}} {A B Z : Over S} (f : A ⟶ B) :
    IsPullback (fst A Z) (f ⊗ₘ 𝟙 Z) f (fst B Z) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd B Z)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t => t ≫ snd B Z) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

private theorem targetPullback (g : G.points) :
    IsPullback (fst (oppositeUnipotentVariety G).toOver (flagVariety G).toOver).left
      (flagChartMorphism G g ⊗ₘ 𝟙 (flagVariety G).toOver).left
      (flagChartMorphism G g).left
      (fst (flagVariety G).toOver (flagVariety G).toOver).left :=
  (tensor_fst_pullback (flagChartMorphism G g)).map (Over.forget _)

private def pairCover :
    Scheme.OpenCover ((flagVariety G).toOver ⊗ (flagVariety G).toOver).left :=
  Scheme.Cover.copy
    ((flagSchemeCover G).pullback₁ (fst (flagVariety G).toOver (flagVariety G).toOver).left)
    G.points (fun _ => ((oppositeUnipotentVariety G).toOver ⊗ (flagVariety G).toOver).left)
    (fun g => (flagChartMorphism G g ⊗ₘ 𝟙 (flagVariety G).toOver).left)
    (Equiv.refl _) (fun g => (targetPullback G g).flip.isoPullback)
    (fun g => (targetPullback G g).flip.isoPullback_hom_fst.symm)

private theorem pairPullback (g : G.points) :
    IsPullback (flagBundleChart G Y g) (localPair G Y j g).left
      (bundlePair G Y j) (flagChartMorphism G g ⊗ₘ 𝟙 (flagVariety G).toOver).left := by
  have houter : IsPullback (flagBundleChart G Y g)
      ((localPair G Y j g).left ≫
        (fst (oppositeUnipotentVariety G).toOver (flagVariety G).toOver).left)
      (bundlePair G Y j ≫ (fst (flagVariety G).toOver (flagVariety G).toOver).left)
      (flagChartMorphism G g).left := by
    rw [bundlePair_fst, ← Over.comp_left, localPair_fst]
    exact (flagBundlePullback G Y g).flip
  exact houter.of_bot (bundlePair_chart G Y j g) (targetPullback G g).flip

private theorem bundlePair_isClosed [IsClosedImmersion j.left] :
    IsClosedImmersion (bundlePair G Y j) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (pairCover G)
  intro g
  change G.points at g
  change IsClosedImmersion (pullback.snd (bundlePair G Y j)
    (flagChartMorphism G g ⊗ₘ 𝟙 (flagVariety G).toOver).left)
  rw [← (pairPullback G Y j g).isoPullback_inv_snd]
  have := localPair_isClosed G Y j g
  infer_instance


/-- An equivariant closed flag inclusion gives a closed associated two-flag correspondence. -/
theorem flagBundlePair_isClosed [IsClosedImmersion j.left] :
    IsClosedImmersion (pullback.lift (flagBundleProjection G Y) (flagBundleMap G Y j)
      (flagBundleMap_toSpec G Y j).symm) :=
  bundlePair_isClosed G Y j

end SchubertGeometry
