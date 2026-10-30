import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Frames
import OrbitComplexity.SchubertGeometry.BSDH.Construction

/-! # The determinant-power section on the BSDH word -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions

noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem frame_condition (N : ℕ) (gh : G.points × G.points) :
    (flagGlueData G).toGlueData.diagram.fst gh ≫ determinantFlagFrame G N gh.1 =
      (flagGlueData G).toGlueData.diagram.snd gh ≫ determinantFlagFrame G N gh.2 := by
  change (flagOverlapInclusion G gh.1 gh.2).left ≫ determinantFlagFrame G N gh.1 =
    ((flagTransition G gh.1 gh.2).left ≫
      (flagOverlapInclusion G gh.2 gh.1).left) ≫ determinantFlagFrame G N gh.2
  rw [← Over.comp_left, flagTransition_comp]
  exact determinantFlagFrame_overlap G N gh.1 gh.2

/-- The regular coefficient frames glue to a section of the full associated character line. -/
def determinantFlagSection (N : ℕ) :
    (flagVariety G).scheme ⟶ determinantLineScheme G N :=
  Multicoequalizer.desc (flagGlueData G).toGlueData.diagram _
    (determinantFlagFrame G N) (frame_condition G N)

/-- On every chart the glued section is the original determinant-power frame. -/
theorem determinantFlagSection_chart (N : ℕ) (g : G.points) :
    (flagChartMorphism G g).left ≫ determinantFlagSection G N =
      determinantFlagFrame G N g := by
  change (flagGlueData G).ι g ≫ _ = _
  exact Multicoequalizer.π_desc (flagGlueData G).toGlueData.diagram _
    (determinantFlagFrame G N) (frame_condition G N) g

/-- The glued determinant map is a section of the associated-line projection. -/
theorem determinantFlagSection_projection (N : ℕ) :
    determinantFlagSection G N ≫ determinantLineProjection G N =
      𝟙 (flagVariety G).scheme := by
  apply (flagSchemeCover G).hom_ext
  intro g
  change G.points at g
  change (flagChartMorphism G g).left ≫
      (determinantFlagSection G N ≫ determinantLineProjection G N) =
    (flagChartMorphism G g).left ≫ 𝟙 _
  rw [← Category.assoc, determinantFlagSection_chart,
    determinantFlagFrame_projection, Category.comp_id]

/-- The line on the BSDH scheme is the pullback of the same full-character associated line. -/
def wordDeterminantLine (N : ℕ) (word : List G.rootBase.support) :
    Over (bsdhScheme G word) :=
  Over.mk (pullback.fst (bsdhMap G word) (determinantLineProjection G N))

/-- The endpoint pulls the fixed determinant-power section to the BSDH word. -/
def wordDeterminantSection (N : ℕ) (word : List G.rootBase.support) :
    bsdhScheme G word ⟶ (wordDeterminantLine G N word).left :=
  pullback.lift (𝟙 _) (bsdhMap G word ≫ determinantFlagSection G N)
    (by rw [Category.id_comp, Category.assoc, determinantFlagSection_projection,
      Category.comp_id])

/-- The word section is a section of its pullback line bundle. -/
theorem wordDeterminantSection_projection (N : ℕ) (word : List G.rootBase.support) :
    wordDeterminantSection G N word ≫ (wordDeterminantLine G N word).hom =
      𝟙 (bsdhScheme G word) :=
  pullback.lift_fst _ _ _

/-- Its associated-line image is the fixed global section evaluated at the endpoint. -/
theorem wordDeterminantSection_endpoint (N : ℕ) (word : List G.rootBase.support) :
    wordDeterminantSection G N word ≫
        pullback.snd (bsdhMap G word) (determinantLineProjection G N) =
      bsdhMap G word ≫ determinantFlagSection G N :=
  pullback.lift_snd _ _ _

/-- Every regular endpoint frame reads the same coefficient section on the word. -/
theorem wordDeterminantSection_frame (N : ℕ) (word : List G.rootBase.support)
    {X : Scheme.{u}} (j : X ⟶ bsdhScheme G word) (g : G.points)
    (a : X ⟶ (oppositeUnipotentVariety G).scheme)
    (ha : a ≫ (flagChartMorphism G g).left = j ≫ bsdhMap G word) :
    j ≫ wordDeterminantSection G N word ≫
        pullback.snd (bsdhMap G word) (determinantLineProjection G N) =
      a ≫ determinantFlagFrame G N g := by
  let s : bsdhScheme G word ⟶
      pullback (bsdhMap G word) (determinantLineProjection G N) :=
    wordDeterminantSection G N word
  change j ≫ s ≫ pullback.snd (bsdhMap G word) (determinantLineProjection G N) = _
  have hs : s ≫ pullback.snd (bsdhMap G word) (determinantLineProjection G N) =
      bsdhMap G word ≫ determinantFlagSection G N :=
    wordDeterminantSection_endpoint G N word
  calc
    _ = j ≫ (bsdhMap G word ≫ determinantFlagSection G N) :=
      congrArg (fun q : bsdhScheme G word ⟶ determinantLineScheme G N => j ≫ q) hs
    _ = (j ≫ bsdhMap G word) ≫ determinantFlagSection G N :=
      (Category.assoc _ _ _).symm
    _ = (a ≫ (flagChartMorphism G g).left) ≫ determinantFlagSection G N :=
      congrArg (fun q => q ≫ determinantFlagSection G N) ha.symm
    _ = a ≫ determinantFlagFrame G N g := by
      rw [Category.assoc, determinantFlagSection_chart]

end SchubertGeometry.ProjectiveLine
