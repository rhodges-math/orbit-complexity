import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorTransitions
import OrbitComplexity.GroupActions.Varieties.ProductImmersions

/-! # Product charts for the original flag torsor and its character equation -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private theorem tensor_fst_pullback {S : Scheme.{u}} {A B Y : Over S} (f : A ⟶ B) :
    IsPullback (fst A Y) (f ⊗ₘ 𝟙 Y) f (fst B Y) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd B Y)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t => t ≫ snd B Y) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev U := (oppositeUnipotentVariety G).toOver
private abbrev B := (borelVariety G).toOver
private abbrev E := U G ⊗ B G
private abbrev Q := E G ⊗ B G
private abbrev H := (reductiveVariety G).toOver

/-- The original group-valued flag-torsor chart with its Borel coordinate. -/
def characterTorsorChart (g : G.points) : E G ⟶ H G :=
  (flagTorsorIso G g).hom ≫
    pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G)

/-- The product chart is Cartesian over its original flag chart. -/
theorem characterTorsorPullback (g : G.points) :
    IsPullback (fst (U G) (B G)) (characterTorsorChart G g)
      (flagChartMorphism G g) (flagQuotientMorphism G) := by
  apply IsPullback.of_iso_pullback _ (flagTorsorIso G g) (flagTorsorIso_fst G g) rfl
  constructor
  calc
    fst (U G) (B G) ≫ flagChartMorphism G g =
        ((flagTorsorIso G g).hom ≫
          pullback.fst (flagChartMorphism G g) (flagQuotientMorphism G)) ≫
            flagChartMorphism G g := by rw [flagTorsorIso_fst]
    _ = characterTorsorChart G g ≫ flagQuotientMorphism G := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      rfl

/-- The product chart into the flag torsor is an open immersion. -/
instance characterTorsorChart_isOpen (g : G.points) :
    IsOpenImmersion (characterTorsorChart G g).left := by
  have h : IsPullback (fst (U G) (B G)).left (characterTorsorChart G g).left
      (flagChartMorphism G g).left (flagQuotientMorphism G).left :=
    (characterTorsorPullback G g).map (Over.forget (Spec (.of K)))
  exact MorphismProperty.of_isPullback h (flagChartMorphism_isOpen G g)

/-- The same product chart, together with the original right Borel multiplier. -/
def characterPairChart (g : G.points) : Q G ⟶ H G ⊗ B G :=
  MonoidalCategory.tensorHom (C := Over (Spec (.of K)))
    (X₁ := E G) (Y₁ := H G) (X₂ := B G) (Y₂ := B G)
    (characterTorsorChart G g) (𝟙 (B G))

/-- The domain of the original right-character equation has the same Cartesian chart. -/
theorem characterPairPullback (g : G.points) :
    IsPullback (fst (E G) (B G) ≫ fst (U G) (B G)) (characterPairChart G g)
      (flagChartMorphism G g)
      (fst (H G) (B G) ≫ flagQuotientMorphism G) :=
  (tensor_fst_pullback (A := E G) (B := H G) (Y := B G)
    (characterTorsorChart G g)).paste_horiz (characterTorsorPullback G g)

/-- The product chart for the character relation is an open immersion. -/
instance characterPairChart_isOpen (g : G.points) :
    IsOpenImmersion (characterPairChart G g).left := by
  unfold characterPairChart
  infer_instance

/-- Multiplication in the local Borel coordinate is the original group right action. -/
theorem characterTorsorChart_mul (g : G.points) :
    lift (fst (E G) (B G) ≫ fst (U G) (B G))
        ((fst (E G) (B G) ≫ snd (U G) (B G)) * snd (E G) (B G)) ≫
        characterTorsorChart G g =
      characterPairChart G g ≫
        (fst (H G) (B G) * (snd (H G) (B G) ≫ borelInclusion G)) := by
  have h := flagTorsorIso_mul G g (Q G)
    (fst (E G) (B G) ≫ fst (U G) (B G))
    (fst (E G) (B G) ≫ snd (U G) (B G)) (snd (E G) (B G))
  have hl : lift (fst (E G) (B G) ≫ fst (U G) (B G))
      (fst (E G) (B G) ≫ snd (U G) (B G)) = fst (E G) (B G) := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  rw [hl] at h
  simpa only [characterTorsorChart, characterPairChart, MonObj.comp_mul,
    Category.assoc, tensorHom_fst, tensorHom_snd_assoc, Category.id_comp] using h

end SchubertGeometry.CharacterLine
