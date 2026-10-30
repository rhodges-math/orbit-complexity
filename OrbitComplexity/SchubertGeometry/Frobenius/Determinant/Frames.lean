import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Morphism
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.BundleSections

/-! # Associated-line frames for the determinant power -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups TauCeti GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem borelReduced : IsReduced (G.borelAlgebra.obj : Type u) := by
  let : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := G.borel_smooth
  exact TauCeti.isReduced_of_smooth K (G.borelAlgebra.obj : Type u)

attribute [local instance] borelReduced

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_smul {X H Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver Y.toOver] (b : X.toOver ⟶ H.toOver)
    (f : X.toOver ⟶ Y.toOver) (x : X.points) :
    Variety.mapPoints (b • f) x = Variety.mapPoints b x • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_smul]
  change X.pointsEquivOverHom x ≫ (b • f) =
    (X.pointsEquivOverHom x ≫ b) • (X.pointsEquivOverHom x ≫ f)
  exact ModObj.comp_smul _ _ _

/-- The inverse fibre action cancels the right character of the regular coefficient. -/
theorem positiveDetPowerMorphism_cancel (N : ℕ) (X : Variety K)
    (a : X.toOver ⟶ (reductiveVariety G).toOver)
    (b : X.toOver ⟶ (borelVariety G).toOver) :
    letI := characterLineAction G (G.positiveRootCharacter ^ N)
    b • ((a * (b ≫ borelInclusion G)) ≫
        DeterminantSection.positiveDetPowerMorphism G N) =
      a ≫ DeterminantSection.positiveDetPowerMorphism G N := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  apply Variety.mapPoints_injective
  funext x
  let g := (reductivePointsMulEquiv G).symm (Variety.mapPoints a x)
  let q := Variety.mapPoints b x
  have ha : Variety.mapPoints a x = reductivePointsEquiv G g :=
    ((reductivePointsMulEquiv G).apply_symm_apply _).symm
  have hm : Variety.mapPoints (a * (b ≫ borelInclusion G)) x =
      reductivePointsEquiv G (g * (borelPointsMulEquiv G q : G.points)) := by
    rw [mapPoints_mul, Variety.mapPoints_comp, borelInclusion_points, ha]
    exact ((reductivePointsMulEquiv G).map_mul g (borelPointsMulEquiv G q)).symm
  rw [mapPoints_smul, Variety.mapPoints_comp, hm,
    DeterminantSection.positiveDetPowerMorphism_points, characterLineAction_smul,
    Equiv.symm_apply_apply, Variety.mapPoints_comp, ha,
    DeterminantSection.positiveDetPowerMorphism_points,
    DeterminantSection.positiveDetPower_right_borel]
  apply congrArg (additivePointsEquiv K)
  let c := borelCharacterUnit G (G.positiveRootCharacter ^ N)
    ((affineGroupPointsMulEquiv K G.borelAlgebra).symm q)
  change (↑c⁻¹ : K) * ((c : K) * g.ofConv (DeterminantSection.positiveDetPower G N)) =
    g.ofConv (DeterminantSection.positiveDetPower G N)
  calc
    _ = ((c⁻¹ * c : Kˣ) : K) *
        g.ofConv (DeterminantSection.positiveDetPower G N) := by
      rw [Units.val_mul, mul_assoc]
    _ = _ := by rw [inv_mul_cancel, Units.val_one, one_mul]

/-- The total space of the inverse-character line for the fixed determinant power. -/
def determinantLineScheme (N : ℕ) : Scheme.{u} :=
  letI := characterLineAction G (G.positiveRootCharacter ^ N)
  flagBundleScheme G (additiveVariety K)

/-- The associated line projects to the original flag variety. -/
def determinantLineProjection (N : ℕ) :
    determinantLineScheme G N ⟶ (flagVariety G).scheme :=
  letI := characterLineAction G (G.positiveRootCharacter ^ N)
  flagBundleProjection G (additiveVariety K)

/-- The regular determinant power gives a section in every unipotent frame. -/
def determinantFlagFrame (N : ℕ) (g : G.points) :
    (oppositeUnipotentVariety G).scheme ⟶ determinantLineScheme G N :=
  letI := characterLineAction G (G.positiveRootCharacter ^ N)
  (lift (𝟙 (oppositeUnipotentVariety G).toOver)
    (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
      flagBundleChart G (additiveVariety K) g

/-- Each frame section projects to its flag chart. -/
theorem determinantFlagFrame_projection (N : ℕ) (g : G.points) :
    determinantFlagFrame G N g ≫ determinantLineProjection G N =
      (flagChartMorphism G g).left := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  change (lift (𝟙 (oppositeUnipotentVariety G).toOver)
      (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
      flagBundleChart G (additiveVariety K) g ≫ flagBundleProjection G (additiveVariety K) = _
  rw [flagBundleChart_projection]
  change (lift (𝟙 (oppositeUnipotentVariety G).toOver)
      (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N) ≫
      fst (oppositeUnipotentVariety G).toOver (additiveVariety K).toOver ≫
        flagChartMorphism G g).left = _
  rw [lift_fst_assoc, Category.id_comp]

/-- The same coefficient sections agree in the associated line on overlaps. -/
theorem determinantFlagFrame_overlap (N : ℕ) (g h : G.points) :
    (flagOverlapInclusion G g h).left ≫ determinantFlagFrame G N g =
      (flagOverlapCoordinate G g h).left ≫ determinantFlagFrame G N h := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  let X := flagOverlapVariety G g h
  let f := flagOverlapInclusion G g h
  let k := flagOverlapCoordinate G g h
  let b := flagOverlapBorel G g h
  let y := f ≫ flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N
  let r : X.toOver ⟶ X.toOver ⊗ (additiveVariety K).toOver := lift (𝟙 X.toOver) y
  have hfibre : b • y = k ≫ flagChartMap G h ≫
      DeterminantSection.positiveDetPowerMorphism G N := by
    have hc := positiveDetPowerMorphism_cancel G N X (k ≫ flagChartMap G h) b
    rw [← flagTorsor_section G g h] at hc
    simpa only [Category.assoc] using hc
  have hl : r ≫ (f ⊗ₘ 𝟙 (additiveVariety K).toOver) = lift f y := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [r]
    · simp [r]
  have hr : r ≫ lift (fst X.toOver (additiveVariety K).toOver ≫ k)
      ((fst X.toOver (additiveVariety K).toOver ≫ b) •
        snd X.toOver (additiveVariety K).toOver) = lift k (b • y) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [r]
    · simp [r, ModObj.comp_smul]
  have hs := sectionBundle_change G X (additiveVariety K) g h f k b (flagTorsor_section G g h)
  have ht := congrArg (fun q => r.left ≫ q) hs
  have ht' : (lift f y).left ≫ flagBundleChart G (additiveVariety K) g =
      (lift k (b • y)).left ≫ flagBundleChart G (additiveVariety K) h := by
    simpa only [← Over.comp_left, ← Category.assoc, hl, hr] using ht
  rw [hfibre] at ht'
  have hg : f ≫ lift (𝟙 (oppositeUnipotentVariety G).toOver)
      (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N) = lift f y := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [y]
  have hh : k ≫ lift (𝟙 (oppositeUnipotentVariety G).toOver)
      (flagChartMap G h ≫ DeterminantSection.positiveDetPowerMorphism G N) =
      lift k (k ≫ flagChartMap G h ≫ DeterminantSection.positiveDetPowerMorphism G N) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hgl : (lift f y).left = f.left ≫
      (lift (𝟙 (oppositeUnipotentVariety G).toOver)
        (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N)).left := by
    simpa only [Over.comp_left] using congrArg
      (fun q : X.toOver ⟶ (oppositeUnipotentVariety G).toOver ⊗
        (additiveVariety K).toOver => q.left) hg.symm
  have hhl :
      (lift k (k ≫ flagChartMap G h ≫ DeterminantSection.positiveDetPowerMorphism G N)).left =
      k.left ≫ (lift (𝟙 (oppositeUnipotentVariety G).toOver)
        (flagChartMap G h ≫ DeterminantSection.positiveDetPowerMorphism G N)).left := by
    simpa only [Over.comp_left] using congrArg
      (fun q : X.toOver ⟶ (oppositeUnipotentVariety G).toOver ⊗
        (additiveVariety K).toOver => q.left) hh.symm
  change f.left ≫ _ = k.left ≫ _
  calc
    _ = (lift f y).left ≫ flagBundleChart G (additiveVariety K) g := by
      rw [hgl]
      simp only [determinantFlagFrame, Category.assoc]
      rfl
    _ = (lift k (k ≫ flagChartMap G h ≫
        DeterminantSection.positiveDetPowerMorphism G N)).left ≫
          flagBundleChart G (additiveVariety K) h := ht'
    _ = _ := by
      rw [hhl]
      simp only [determinantFlagFrame, Category.assoc]
      rfl

end SchubertGeometry.ProjectiveLine
