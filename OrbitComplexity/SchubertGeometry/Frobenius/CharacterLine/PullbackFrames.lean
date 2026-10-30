import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Evaluation
import OrbitComplexity.GroupActions.Modules.UnitCoherence
import Batteries.Tactic.Lint

/-! # Pullback frames of the original word character section -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open MonoidalCategory

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private theorem inverse_comp_factor {D : Type*} [Category D] {A B C T : D}
    (c : A ⟶ B) (e : B ≅ C) (f : C ≅ T) (g : A ≅ T)
    (h : c ≫ e.hom ≫ f.hom = g.hom) : g.inv ≫ c = f.inv ≫ e.inv := by
  apply (cancel_mono e.hom).1
  apply (cancel_mono f.hom).1
  simpa [Category.assoc] using congrArg (fun k => g.inv ≫ k) h

private theorem section_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (H : D ⥤ E) (J : C ⥤ E) (α : J ⟶ F ⋙ H)
    {U M : C} {V : D} {W : E}
    (a : W ⟶ J.obj U) (b : W ⟶ H.obj V) (c : V ⟶ F.obj U)
    (hu : a ≫ α.app U = b ≫ H.map c) (s : U ⟶ M) :
    (a ≫ J.map s) ≫ α.app M = b ≫ H.map (c ≫ F.map s) := by
  rw [Category.assoc, α.naturality, ← Category.assoc, hu, Category.assoc]
  change b ≫ H.map c ≫ H.map (F.map s) = _
  rw [← H.map_comp]

private theorem section_frame_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U M : C} {V : D} (e : F.obj U ≅ V)
    (s : U ⟶ M) (t : M ⟶ U) (a : U ⟶ U) (b : V ⟶ V)
    (hs : s ≫ t = a) (hn : F.map a ≫ e.hom = e.hom ≫ b) :
    (e.inv ≫ F.map s) ≫ F.map t ≫ e.hom = b := by
  calc
    (e.inv ≫ F.map s) ≫ F.map t ≫ e.hom =
        e.inv ≫ F.map (s ≫ t) ≫ e.hom := by
      rw [F.map_comp]
      simp [Category.assoc]
    _ = e.inv ≫ F.map a ≫ e.hom := by rw [hs]
    _ = e.inv ≫ (e.hom ≫ b) := by rw [hn]
    _ = b := by simp

private theorem iso_inv_comp {D : Type*} [Category D] {A B C : D}
    (e : A ≅ B) {f : B ⟶ C} {g : A ⟶ C} (h : e.hom ≫ f = g) :
    e.inv ≫ g = f := by
  rw [← h, Iso.inv_hom_id_assoc]

private theorem section_iso_transport {C D : Type*} [Category C] [Category D]
    (R P : C ⥤ D) (α : R ≅ P) {U M : C} {V : D} (e : P.obj U ≅ V)
    (u : R.obj U ⟶ V) (s : U ⟶ M) (k : R.obj M ⟶ V) (b : V ⟶ V)
    (hs : R.map s ≫ k = u ≫ b) (hu : α.inv.app U ≫ u = e.hom) :
    (e.inv ≫ P.map s) ≫ (α.inv.app M ≫ k) = b := by
  calc
    (e.inv ≫ P.map s) ≫ (α.inv.app M ≫ k) =
        e.inv ≫ (P.map s ≫ α.inv.app M) ≫ k := by simp [Category.assoc]
    _ = e.inv ≫ (α.inv.app U ≫ R.map s) ≫ k := by rw [α.inv.naturality]
    _ = e.inv ≫ α.inv.app U ≫ (R.map s ≫ k) := by simp [Category.assoc]
    _ = e.inv ≫ α.inv.app U ≫ (u ≫ b) := by rw [hs]
    _ = e.inv ≫ (α.inv.app U ≫ u) ≫ b := by simp [Category.assoc]
    _ = e.inv ≫ e.hom ≫ b := by rw [hu]
    _ = b := by simp

private theorem pair_substitute {D : Type*} [Category D] {A B C T : D}
    {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ C} (h : a ≫ b = c) (k : C ⟶ T) :
    a ≫ (b ≫ k) = c ≫ k :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ k) h)

private theorem cancel_iso_frame {D : Type*} [Category D] {A B C T : D}
    (e : B ≅ C) {c : A ⟶ C} {d : A ⟶ B} (h : c ≫ e.inv = d) (k : C ⟶ T) :
    d ≫ (e.hom ≫ k) = c ≫ k := by
  rw [← h, Category.assoc, Iso.inv_hom_id_assoc]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: pullSection"

private def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : (𝟙_ Y.Modules) ⟶ M) : (𝟙_ X.Modules) ⟶ (pullback f).obj M :=
  (pullbackObjUnitIso f).inv ≫ (pullback f).map s

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: pullSection_comp"

private theorem pullSection_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : (𝟙_ Z.Modules) ⟶ M) :
    pullSection (f ≫ g) M s ≫ (pullbackComp f g).inv.app M =
      pullSection f ((pullback g).obj M) (pullSection g M s) := by
  have hu := inverse_comp_factor
    ((pullbackComp f g).inv.app (𝟙_ Z.Modules))
    ((pullback f).mapIso (pullbackObjUnitIso g))
    (pullbackObjUnitIso f) (pullbackObjUnitIso (f ≫ g)) (pullbackObjUnitIso_comp f g)
  exact section_map_comp (pullback g) (pullback f) (pullback (f ≫ g))
    (pullbackComp f g).inv (pullbackObjUnitIso (f ≫ g)).inv
    (pullbackObjUnitIso f).inv (pullbackObjUnitIso g).inv hu s

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: pullSection_congr"

private theorem pullSection_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (s : (𝟙_ Y.Modules) ⟶ M) :
    pullSection f M s ≫ (pullbackCongr h).hom.app M = pullSection g M s := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact Category.comp_id (pullSection f M s)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: pullSection_frame"

private theorem pullSection_frame {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : (𝟙_ Y.Modules) ⟶ M) (e : M ≅ (𝟙_ Y.Modules)) (r : Γ(Y, ⊤))
    (hs : s ≫ e.hom = globalSectionsSmul (𝟙_ Y.Modules) r) :
    pullSection f M s ≫ (pullback f).map e.hom ≫ (pullbackObjUnitIso f).hom =
      globalSectionsSmul (𝟙_ X.Modules) (f.appTop r) := by
  have hn := (congrArg (fun q => q ≫ (pullbackObjUnitIso f).hom)
    (pullback_map_globalSectionsSmul f (𝟙_ Y.Modules) r)).trans
      (globalSectionsSmul_naturality (pullbackObjUnitIso f).hom (f.appTop r))
  exact section_frame_transport (pullback f) (pullbackObjUnitIso f) s e.hom
    (globalSectionsSmul (𝟙_ Y.Modules) r)
    (globalSectionsSmul (𝟙_ X.Modules) (f.appTop r)) hs hn

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev U := (oppositeUnipotentVariety G).scheme
private abbrev F := (flagVariety G).scheme

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: flagDeterminantPullback_frame"

/-- A pulled-back flag chart frame reads the pullback of the determinant-power function. -/
theorem flagDeterminantPullback_frame (N : ℕ) (g : G.points)
    {X : Scheme.{u}} (a : X ⟶ U G) :
    (pullbackObjUnitIso (a ≫ (flagChartMorphism G g).left)).inv ≫
        (pullback (a ≫ (flagChartMorphism G g).left)).map
          (flagDeterminantModuleSection G N) ≫
        (flagCharacterPullbackIso G g (G.positiveRootCharacter ^ N) a).hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf)
        ((a ≫ (flagChartMap G g).left).appTop
          (DeterminantSection.positiveDetPowerFunction G N)) := by
  let j : U G ⟶ F G := (flagChartMorphism G g).left
  let M : (F G).Modules := flagCharacterModule G (G.positiveRootCharacter ^ N)
  let s : SheafOfModules.unit (F G).ringCatSheaf ⟶ M := flagDeterminantModuleSection G N
  let e : (pullback j).obj M ≅ SheafOfModules.unit (U G).ringCatSheaf :=
    ((restrictFunctorIsoPullback j).app M).symm ≪≫
      flagCharacterChartIso G g (G.positiveRootCharacter ^ N)
  let r : Γ(U G, ⊤) := (flagChartMap G g).left.appTop
    (DeterminantSection.positiveDetPowerFunction G N)
  have he : pullSection j M s ≫ e.hom =
      globalSectionsSmul (SheafOfModules.unit (U G).ringCatSheaf) r := by
    have hu := iso_inv_comp ((restrictFunctorIsoPullback j).app (𝟙_ (F G).Modules))
      (GroupActions.restrictPullback_unit j)
    exact section_iso_transport (restrictFunctor j) (pullback j)
      (restrictFunctorIsoPullback j) (pullbackObjUnitIso j) (restrictUnitIso j).hom s
      (flagCharacterChartIso G g (G.positiveRootCharacter ^ N)).hom
      (globalSectionsSmul (SheafOfModules.unit (U G).ringCatSheaf) r)
      (flagDeterminantModuleSection_chart G N g) hu
  change pullSection (a ≫ j) M s ≫
      ((pullbackComp a j).inv.app M ≫
        (pullback a).map e.hom ≫ (pullbackObjUnitIso a).hom) = _
  have hcomp := pair_substitute (pullSection_comp a j M s)
    ((pullback a).map e.hom ≫ (pullbackObjUnitIso a).hom)
  have hframe := pullSection_frame a ((pullback j).obj M) (pullSection j M s) e r he
  have hr : (a ≫ (flagChartMap G g).left).appTop
        (DeterminantSection.positiveDetPowerFunction G N) = a.appTop r :=
    ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop a (flagChartMap G g).left)
      (DeterminantSection.positiveDetPowerFunction G N)
  exact hcomp.trans (hframe.trans
    (congrArg (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf)) hr.symm))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: wordDeterminantModule_frame"

/-- The word character frame evaluates its determinant section at the pulled-back
 determinant-power function. -/
theorem wordDeterminantModule_frame (N : ℕ) (word : List G.rootBase.support)
    {X : Scheme.{u}} (k : X ⟶ bsdhScheme G word) (g : G.points) (a : X ⟶ U G)
    (h : a ≫ (flagChartMorphism G g).left = k ≫ bsdhMap G word) :
    (pullbackObjUnitIso k).inv ≫
        (pullback k).map (wordDeterminantModuleSection G N word) ≫
        (wordCharacterFrameIso G word (G.positiveRootCharacter ^ N) k g a h).hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf)
        ((a ≫ (flagChartMap G g).left).appTop
          (DeterminantSection.positiveDetPowerFunction G N)) := by
  let M : (F G).Modules := flagCharacterModule G (G.positiveRootCharacter ^ N)
  let s : SheafOfModules.unit (F G).ringCatSheaf ⟶ M := flagDeterminantModuleSection G N
  change pullSection k ((pullback (bsdhMap G word)).obj M)
      (pullSection (bsdhMap G word) M s) ≫
      ((pullbackComp k (bsdhMap G word)).hom.app M ≫
        (pullbackCongr h.symm).hom.app M ≫
        (flagCharacterPullbackIso G g (G.positiveRootCharacter ^ N) a).hom) = _
  have hcancel := cancel_iso_frame ((pullbackComp k (bsdhMap G word)).app M)
    (pullSection_comp k (bsdhMap G word) M s)
    ((pullbackCongr h.symm).hom.app M ≫
      (flagCharacterPullbackIso G g (G.positiveRootCharacter ^ N) a).hom)
  have hcongr := pair_substitute (pullSection_congr h.symm M s)
    (flagCharacterPullbackIso G g (G.positiveRootCharacter ^ N) a).hom
  exact hcancel.trans (hcongr.trans (flagDeterminantPullback_frame G N g a))

end SchubertGeometry.CharacterLine
