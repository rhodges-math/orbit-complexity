import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CharacterFramePowers
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The append coframes as character evaluations

The degree comparison and its chart equation identify the constructed
polynomial coframe with the regular append-lift coframe for every character
power. Restriction/pullback naturality is combined over arbitrary categories.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private appendFlagModule appendRawCoframe appendCoframe
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private appendDegreeMap appendDegreeMap_frame
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendDegree
open private appendDegreeIso_hom
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections

private theorem pullback_frame {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F G : C ⥤ D) (eta : F ≅ G) {M N : C} {T : D}
    (d : M ⟶ N) (e : F.obj N ⟶ T) (r : G.obj M ⟶ T)
    (h : F.map d ≫ e = eta.hom.app M ≫ r) :
    G.map d ≫ eta.inv.app N ≫ e = r := by
  calc
    _ = (G.map d ≫ eta.inv.app N) ≫ e := (Category.assoc _ _ _).symm
    _ = (eta.inv.app M ≫ F.map d) ≫ e :=
      congrArg (fun t => t ≫ e) (eta.inv.naturality d)
    _ = eta.inv.app M ≫ (F.map d ≫ e) := Category.assoc _ _ _
    _ = eta.inv.app M ≫ (eta.hom.app M ≫ r) := congrArg (fun t => eta.inv.app M ≫ t) h
    _ = r := by
      change (eta.app M).inv ≫ (eta.app M).hom ≫ r = r
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem coframe_fusion {C D E : Type v}
    [Category.{w} C] [Category.{w} D] [Category.{w} E]
    (H : C ⥤ D) (F : D ⥤ E) (J : C ⥤ E) (R : D ⥤ E)
    (eta : H ⋙ F ≅ J) (theta : R ≅ F)
    {U : C} {M N : D} {T : E}
    (c : H.obj U ≅ N) (e : R.obj N ≅ T)
    (b : H.obj U ⟶ M) (d : M ⟶ N) (r : F.obj M ⟶ T)
    (b₀ : H.obj U ⟶ M) (hb : b₀ = b)
    (hc : c.hom = b₀ ≫ d)
    (h : R.map d ≫ e.hom = theta.hom.app M ≫ r)
    (frame : J.obj U ≅ T)
    (hframe : frame = (eta.app U).symm ≪≫ F.mapIso c ≪≫ theta.symm.app N ≪≫ e) :
    frame.hom =
      eta.inv.app U ≫ F.map b ≫ r := by
  subst b₀
  subst frame
  change eta.inv.app U ≫ F.map c.hom ≫ theta.inv.app N ≫ e.hom = _
  have hr := pullback_frame R F theta d e.hom r h
  rw [hc, Functor.map_comp]
  simp only [Category.assoc, hr]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (V : Over (Spec (.of K))) (g : G.points)
    (a : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (.op B) ⟶ V)

/-- The polynomial append coframe is the regular-lift character coframe,
preceded by the specified word and flag pullback comparisons. -/
theorem appendPolynomialFrame_raw (n : ℕ) (j : Fin 2) :
    @Eq ((Scheme.Modules.pullback
      (X := Spec (.of (Polynomial B))) (Y := bsdhScheme G (word ++ [i]))
      (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
        (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2)))
        (bsdhScheme G (word ++ [i]))
        (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c))).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n)
          (word ++ [i])) ⟶
      SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
      (appendPolynomialFrame G word i V g a c hend B p n ⟨j⟩).hom
      ((Scheme.Modules.pullbackComp
        (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B (ULift.{u} (Fin 2)))
        (Z := bsdhScheme G (word ++ [i])) (projectiveLinePolynomialChart B ⟨j⟩)
        (projectiveAppendChart G i B p c)).inv.app
          (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i])) ≫
        (Scheme.Modules.pullback
          (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B (ULift.{u} (Fin 2)))
          (projectiveLinePolynomialChart B ⟨j⟩)).map
          ((Scheme.Modules.pullbackComp
            (X := projectiveScheme B (ULift.{u} (Fin 2)))
            (Y := bsdhScheme G (word ++ [i])) (Z := (flagVariety G).scheme)
            (projectiveAppendChart G i B p c)
            (bsdhMap G (word ++ [i]))).hom.app
              (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ≫
        appendRawCoframe G word i V g a c hend B p (G.positiveRootCharacter ^ n) j) := by
  exact @coframe_fusion.{u + 1,u}
    (bsdhScheme G (word ++ [i])).Modules
    (projectiveScheme B (ULift.{u} (Fin 2))).Modules
    (Spec (.of (Polynomial B))).Modules
    (inferInstanceAs (Category.{u} (bsdhScheme G (word ++ [i])).Modules))
    (inferInstanceAs (Category.{u} (projectiveScheme B (ULift.{u} (Fin 2))).Modules))
    (inferInstanceAs (Category.{u} (Spec (.of (Polynomial B))).Modules))
    (Scheme.Modules.pullback
      (X := projectiveScheme B (ULift.{u} (Fin 2)))
      (Y := bsdhScheme G (word ++ [i])) (projectiveAppendChart G i B p c))
    (Scheme.Modules.pullback
      (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B (ULift.{u} (Fin 2)))
      (projectiveLinePolynomialChart B ⟨j⟩))
    (Scheme.Modules.pullback
      (X := Spec (.of (Polynomial B))) (Y := bsdhScheme G (word ++ [i]))
      (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
        (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2)))
        (bsdhScheme G (word ++ [i]))
        (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c)))
    (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart B ⟨j⟩))
    (Scheme.Modules.pullbackComp
      (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B (ULift.{u} (Fin 2)))
      (Z := bsdhScheme G (word ++ [i])) (projectiveLinePolynomialChart B ⟨j⟩)
      (projectiveAppendChart G i B p c))
    (Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart B ⟨j⟩))
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (appendFlagModule G word i V c B p (G.positiveRootCharacter ^ n))
    (ProjectiveLine.projectiveTransitionModule B (2 * n))
    (SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
    (CharacterLine.appendCharacterDegreeIso G word i V g a c hend B p n)
    (ProjectiveLine.projectiveTransitionChart B (2 * n) ⟨j⟩)
    ((Scheme.Modules.pullbackComp
      (X := projectiveScheme B (ULift.{u} (Fin 2)))
      (Y := bsdhScheme G (word ++ [i])) (Z := (flagVariety G).scheme)
      (projectiveAppendChart G i B p c)
      (bsdhMap G (word ++ [i]))).hom.app
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)))
    (appendDegreeMap G word i V g a c hend B p n)
    (appendRawCoframe G word i V g a c hend B p (G.positiveRootCharacter ^ n) j)
    (((Scheme.Modules.pullbackComp (projectiveAppendChart G i B p c)
      (bsdhMap G (word ++ [i]))).app
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))).hom)
    (by
      have hComp : Scheme.Modules.pullbackComp (projectiveAppendChart G i B p c)
          (bsdhMap G (word ++ [i])) =
          Scheme.Modules.pullbackComp
            (X := projectiveScheme B (ULift.{u} (Fin 2)))
            (Y := bsdhScheme G (word ++ [i])) (Z := (flagVariety G).scheme)
            (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])) := rfl
      exact (Iso.app_hom
        (Scheme.Modules.pullbackComp (projectiveAppendChart G i B p c)
          (bsdhMap G (word ++ [i])))
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))).trans
          (congrArg (fun E => E.hom.app
            (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) hComp))
    (appendDegreeIso_hom G word i V g a c hend B p n)
    ((appendDegreeMap_frame G word i V g a c hend B p n j).trans rfl)
    (appendPolynomialFrame G word i V g a c hend B p n ⟨j⟩) rfl

end SchubertGeometry.RetainedCharacter
