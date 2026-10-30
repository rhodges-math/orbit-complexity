import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorCharts

/-! # Base change of the Borel torsor along a chart coordinate morphism -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u

private theorem tensor_fst_pullback {S : Scheme.{u}} {X U B : Over S} (f : X ⟶ U) :
    IsPullback (fst X B) (f ⊗ₘ 𝟙 B) f (fst U B) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd U B)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t => t ≫ snd U B) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private def torsorGroup (g : G.points) :=
  (flagTorsorIso G g).hom ≫ pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G)

private theorem torsorSquare (g : G.points) :
    IsPullback
      (fst (oppositeUnipotentVariety G).toOver (borelVariety G).toOver)
      (torsorGroup G g) (flagChartMorphism G g) (flagQuotientMorphism G) := by
  apply IsPullback.of_iso_pullback _ (flagTorsorIso G g)
    (flagTorsorIso_fst G g) rfl
  refine ⟨?_⟩
  change _ = (flagTorsorIso G g).hom ≫
    pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G) ≫ flagQuotientMorphism G
  rw [← pullback.condition, ← Category.assoc, flagTorsorIso_fst]

/-- A coordinate morphism pulls back the Borel torsor as a product with Borel. -/
def sectionTorsorIso (X : Over (Spec (CommRingCat.of K)))
    (f : X ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    X ⊗ (borelVariety G).toOver ≅
      pullback (f ≫ flagChartMorphism G g) (flagQuotientMorphism G) :=
  ((tensor_fst_pullback f).paste_vert (torsorSquare G g)).isoPullback

/-- The pulled-back torsor isomorphism preserves its base coordinate. -/
theorem sectionTorsorIso_fst (X : Over (Spec (CommRingCat.of K)))
    (f : X ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    (sectionTorsorIso G X f g).hom ≫
      pullback.fst (f ≫ flagChartMorphism G g) (flagQuotientMorphism G) =
        fst X (borelVariety G).toOver :=
  IsPullback.isoPullback_hom_fst _

/-- Its group projection multiplies the specified section by the Borel coordinate. -/
theorem sectionTorsorIso_group (X : Over (Spec (CommRingCat.of K)))
    (f : X ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    (sectionTorsorIso G X f g).hom ≫
      pullback.snd (f ≫ flagChartMorphism G g) (flagQuotientMorphism G) =
      (fst X (borelVariety G).toOver ≫ f ≫ flagChartMap G g) *
        (snd X (borelVariety G).toOver ≫ borelInclusion G) := by
  rw [sectionTorsorIso, IsPullback.isoPullback_hom_snd]
  simp only [torsorGroup, flagTorsorIso_group, MonObj.comp_mul,
    tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp]

end SchubertGeometry.ProjectiveLine
