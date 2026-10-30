import OrbitComplexity.SchubertGeometry.Normality.Models.BsdhInfinityUnits
import OrbitComplexity.SchubertGeometry.Normality.Models.BsdhInfinityCoeff
import OrbitComplexity.SchubertGeometry.Normality.Models.BsdhBoundary
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveChartTransitions

/-! # The omitted section in the specified projective append chart -/

noncomputable section
namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

private theorem section_base (R : Type u) [CommRing R] (j : ULift.{u} (Fin 2)) :
    projectiveLineSection R j ≫ projectiveToSpec R (ULift.{u} (Fin 2)) = 𝟙 _ := by
  rw [projectiveLineSection, Category.assoc, projectiveLinePolynomialChart_base,
    ← Spec.map_comp]
  rw [show CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
    CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 (CommRingCat.of R) from by
      ext r
      simp]
  exact Spec.map_id _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def infinitySection (i : G.rootBase.support) : 𝟙_ (Over (Spec (.of K))) ⟶
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver :=
  (Over.homMk (V := (projectiveVariety K (ULift.{u} (Fin 2))).toOver)
    (projectiveLineSection K ⟨1⟩) (section_base K ⟨1⟩)) ≫ (simpleSchubertIso G i).inv

private theorem infinity_flag (i : G.rootBase.support) :
    infinitySection G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
      η[(reductiveVariety G).toOver] ≫ flagQuotientMorphism G := by
  apply Over.OverMorphism.ext
  exact simple_infinity_flag G i

private theorem unit_action {T : Over (Spec (.of K))}
    (h : T ⟶ (reductiveVariety G).toOver) :
    h • ((1 : T ⟶ (reductiveVariety G).toOver) ≫ flagQuotientMorphism G) =
      h ≫ flagQuotientMorphism G := by
  let H := reductiveVariety G
  let : ModObj H.toOver H.toOver := ModObj.regular _
  have hu : (1 : T ⟶ (oppositeUnipotentVariety G).toOver) ≫ flagChartMap G 1 = 1 := by
    change ((1 : T ⟶ (oppositeUnipotentVariety G).toOver) ≫
      oppositeUnipotentInclusion G) ≫
        (leftTranslation H (reductivePointsMulEquiv G 1)).hom = 1
    rw [map_one]
    change _ ≫ Variety.translateMorphism H H 1 = 1
    rw [Variety.translateMorphism_one, Category.comp_id, MonObj.one_comp]
  have hc : (1 : T ⟶ (oppositeUnipotentVariety G).toOver) ≫ flagChartMorphism G 1 =
      (1 : T ⟶ (reductiveVariety G).toOver) ≫ flagQuotientMorphism G := by
    rw [← flagChartMap_quotient, ← Category.assoc, hu]
  simpa only [hc, hu, mul_one] using
    flag_action_chart G h (1 : T ⟶ (oppositeUnipotentVariety G).toOver) 1

private theorem bundle_ext (i : G.rootBase.support) {T : Scheme.{u}}
    (x y : T ⟶ flagBundleScheme G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))
    (hπ : x ≫ flagBundleProjection G _ = y ≫ flagBundleProjection G _)
    (hτ : x ≫ flagBundleMap G _
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) =
      y ≫ flagBundleMap G _
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) : x = y := by
  obtain ⟨e, he₁, he₂⟩ := simpleSchubert_incidence G i
  apply (cancel_mono e.hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, he₁] using hπ
  · simpa only [Category.assoc, he₂] using hτ

private theorem append_ext (word : List G.rootBase.support) (i : G.rootBase.support)
    {T : Scheme.{u}} (x y : T ⟶ bsdhScheme G (word ++ [i]))
    (hπ : x ≫ bsdhAppendFst G word i = y ≫ bsdhAppendFst G word i)
    (hτ : x ≫ bsdhMap G (word ++ [i]) = y ≫ bsdhMap G (word ++ [i])) : x = y := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let π := flagBundleProjection G Y
  let e := (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i)
  apply (cancel_mono e.hom).mp
  apply pullback.hom_ext
  · exact hπ
  · apply bundle_ext G i
    · have hx : x ≫ e.hom ≫ pullback.snd (bsdhMap G word) π ≫ π =
          (x ≫ bsdhAppendFst G word i) ≫ bsdhMap G word := by
        simpa only [Category.assoc, bsdhAppendFst, e, π, Y,
          Functor.mapIso_hom, Over.forget_map] using
          congrArg (fun f ↦ x ≫ e.hom ≫ f)
            (pullback.condition (f := bsdhMap G word) (g := π)).symm
      have hy : y ≫ e.hom ≫ pullback.snd (bsdhMap G word) π ≫ π =
          (y ≫ bsdhAppendFst G word i) ≫ bsdhMap G word := by
        simpa only [Category.assoc, bsdhAppendFst, e, π, Y,
          Functor.mapIso_hom, Over.forget_map] using
          congrArg (fun f ↦ y ≫ e.hom ≫ f)
            (pullback.condition (f := bsdhMap G word) (g := π)).symm
      exact hx.trans ((congrArg (fun f ↦ f ≫ bsdhMap G word) hπ).trans hy.symm)
    · have hx := congrArg (fun f ↦ x ≫ f) (bsdhAppendIso_endpoint G word i)
      have hy := congrArg (fun f ↦ y ≫ f) (bsdhAppendIso_endpoint G word i)
      simpa only [Category.assoc, e, Functor.mapIso_hom, Over.forget_map] using
        hx.trans (hτ.trans hy.symm)

private theorem endpoint_from_bundle (word : List G.rootBase.support)
    (i : G.rootBase.support) {T : Scheme.{u}}
    (c : T ⟶ bsdhScheme G (word ++ [i]))
    (r : T ⟶ flagBundleScheme G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))
    (hc : c ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) = r) :
    c ≫ bsdhMap G (word ++ [i]) = r ≫ flagBundleMap G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  let τ := flagBundleMap G
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
  calc
    _ = (c ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))) ≫ τ := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ c ≫ f) (bsdhAppendIso_endpoint G word i).symm
    _ = r ≫ τ := congrArg (fun f ↦ f ≫ τ) hc

private theorem local_infinity (word : List G.rootBase.support) (i : G.rootBase.support)
    (d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G word i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word)
    (U : Over (Spec (.of K))) (b : U ⟶ Over.mk (bsdhToSpec G word))
    (g : G.points) (a : U ⟶ (oppositeUnipotentVariety G).toOver) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∀ (c : U ⊗ Y.toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])))
      (_ : c.left ≫ bsdhAppendFst G word i = (fst U Y.toOver).left ≫ b.left)
      (_ : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
          pullback.snd (bsdhMap G word) (flagBundleProjection G Y) =
        (a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g)
      (_ : a.left ≫ flagSchemeChart G g = b.left ≫ bsdhMap G word),
      (lift (𝟙 U) (toUnit U ≫ infinitySection G i)).left ≫ c.left = b.left ≫ d := by
  dsimp only
  intro c hπ hc ha
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let z := lift (𝟙 U) (toUnit U ≫ infinitySection G i)
  let j := schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let action := (fst (oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMap G g) •
    (snd (oppositeUnipotentVariety G).toOver Y.toOver ≫ j)
  have he : c.left ≫ bsdhMap G (word ++ [i]) =
      (a ⊗ₘ 𝟙 Y.toOver).left ≫ action.left := by
    have h := endpoint_from_bundle G word i c.left
      ((a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g) hc
    rw [Category.assoc, flagBundleChart_map G Y j g] at h
    exact h
  have hz : z ≫ (a ⊗ₘ 𝟙 Y.toOver) ≫ action = a ≫ flagChartMorphism G g := by
    have hj : (𝟙 Y.toOver) ≫ j = j := Category.id_comp j
    calc
      _ = (a ≫ flagChartMap G g) •
          (toUnit U ≫ infinitySection G i ≫ j) := by
        simp only [z, action, ModObj.comp_smul, tensorHom_fst_assoc,
          tensorHom_snd_assoc, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
          Category.assoc, hj]
      _ = _ := by
        dsimp only [j]
        rw [infinity_flag G i]
        change (a ≫ flagChartMap G g) •
          ((1 : U ⟶ (reductiveVariety G).toOver) ≫ flagQuotientMorphism G) = _
        rw [unit_action, Category.assoc, flagChartMap_quotient]
  apply append_ext G word i (z.left ≫ c.left) (b.left ≫ d)
  · calc
      _ = (z ≫ fst U Y.toOver).left ≫ b.left := by rw [Category.assoc, hπ]; rfl
      _ = b.left := by rw [lift_fst]; exact Category.id_comp _
      _ = _ := by
        rw [Category.assoc, hdπ]
        exact (Category.comp_id b.left).symm
  · calc
      _ = (z ≫ (a ⊗ₘ 𝟙 Y.toOver) ≫ action).left := by rw [Category.assoc, he]; rfl
      _ = (a ≫ flagChartMorphism G g).left := congrArg Over.Hom.left hz
      _ = b.left ≫ bsdhMap G word := ha
      _ = _ := by rw [Category.assoc, hdτ]

/-- Chart-one zero in the specified append chart is the omitted-step section. -/
theorem bsdh_omitted_infinity (word : List G.rootBase.support) (i : G.rootBase.support)
    (d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G word i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word)
    (U : Over (Spec (.of K))) (b : U ⟶ Over.mk (bsdhToSpec G word))
    (A : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (.op A) ⟶ U)
    (g : G.points) (a : U ⟶ (oppositeUnipotentVariety G).toOver) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∀ (c : U ⊗ Y.toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])))
      (_ : c.left ≫ bsdhAppendFst G word i = (fst U Y.toOver).left ≫ b.left)
      (_ : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
          pullback.snd (bsdhMap G word) (flagBundleProjection G Y) =
        (a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g)
      (_ : a.left ≫ flagSchemeChart G g = b.left ≫ bsdhMap G word),
      projectiveLineSection A ⟨1⟩ ≫ projectiveAppendChart G i A p c =
        p.left ≫ b.left ≫ d := by
  dsimp only
  intro c hπ hc ha
  let S := (algSpec (.of K)).obj (.op A)
  let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  let z := lift (𝟙 S) (toUnit S ≫ infinitySection G i)
  have hz₁ : z.left ≫ (fst S Y).left = 𝟙 _ :=
    congrArg Over.Hom.left (lift_fst (𝟙 S) (toUnit S ≫ infinitySection G i))
  have hz₂ : z.left ≫ (snd S Y).left =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ projectiveLineSection K ⟨1⟩ ≫
        (simpleSchubertIso G i).inv.left := by
    change (z ≫ snd S Y).left = _
    rw [lift_snd]
    rfl
  have hz : projectiveLineSection A ⟨1⟩ ≫ (simpleBorelLineIso G i A).inv = z.left := by
    apply pullback.hom_ext
    · change (projectiveLineSection A ⟨1⟩ ≫ (simpleBorelLineIso G i A).inv) ≫
          (fst S Y).left = z.left ≫ (fst S Y).left
      exact (Category.assoc _ _ _).trans
        ((simple_infinity_product G i A).1.trans hz₁.symm)
    · change (projectiveLineSection A ⟨1⟩ ≫ (simpleBorelLineIso G i A).inv) ≫
          (snd S Y).left = z.left ≫ (snd S Y).left
      exact (Category.assoc _ _ _).trans
        ((simple_infinity_product G i A).2.trans hz₂.symm)
  have hp : z ≫ (p ⊗ₘ 𝟙 Y) = p ≫ lift (𝟙 U) (toUnit U ≫ infinitySection G i) := by
    apply CartesianMonoidalCategory.hom_ext
    · dsimp only [Y]
      simp only [z, Category.assoc, tensorHom_fst, lift_fst_assoc,
        lift_fst, Category.id_comp]
      exact (Category.comp_id p).symm
    · dsimp only [Y]
      simp only [z, Category.assoc, tensorHom_snd, lift_snd,
        Category.comp_id, comp_toUnit_assoc]
  have hl := local_infinity G word i d hdπ hdτ U b g a c hπ hc ha
  calc
    _ = z.left ≫ ((p ⊗ₘ 𝟙 Y) ≫ c).left := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ f ≫ ((p ⊗ₘ 𝟙 Y) ≫ c).left) hz)
    _ = (p ≫ lift (𝟙 U) (toUnit U ≫ infinitySection G i)).left ≫ c.left :=
      congrArg (fun f ↦ f.left ≫ c.left) hp
    _ = p.left ≫ (b.left ≫ d) := by
      exact (Category.assoc _ _ _).trans (congrArg (fun f ↦ p.left ≫ f) hl)

end SchubertGeometry
