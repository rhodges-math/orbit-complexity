import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
import OrbitComplexity.FrobeniusSplitting.Modules.Sections
import Batteries.Tactic.Lint

/-! # Character evaluation along a regular lift of the flag quotient -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine

private theorem middle_isIso {C : Type v} [Category.{w} C] {A B D E : C}
    (a : A ⟶ B) [IsIso a] (b : B ⟶ D) (c : D ⟶ E) [IsIso c]
    (d : A ⟶ E) [IsIso d] (h : a ≫ b ≫ c = d) : IsIso b := by
  let _ : IsIso (b ≫ c) := IsIso.of_isIso_fac_left h
  exact IsIso.of_isIso_comp_right b c

private theorem isIso_eq {C : Type v} [Category.{w} C] {A B : C}
    {f g : A ⟶ B} (h : f = g) (hf : IsIso f) : IsIso g := by
  subst g
  exact hf

private theorem factor_isIso {C : Type v} [Category.{w} C] {A B D : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D)
    (ha : IsIso a) (hc : IsIso c) (h : a ≫ b = c) : IsIso b :=
  @IsIso.of_isIso_fac_left C _ A B D a b c ha hc h

private theorem compIsIso {C : Type v} [Category.{w} C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (hf : IsIso f) (hg : IsIso g) : IsIso (f ≫ g) :=
  @IsIso.comp_isIso C _ A B D f g hf hg

private def scalarIso {X : Scheme.{u}} (M : X.Modules) (unit : Γ(X, ⊤)ˣ) : M ≅ M where
  hom := globalSectionsSmul M unit
  inv := globalSectionsSmul M (unit⁻¹ : Γ(X, ⊤)ˣ)
  hom_inv_id := by
    rw [← globalSectionsSmul_mul, Units.inv_mul, globalSectionsSmul_one]
  inv_hom_id := by
    rw [← globalSectionsSmul_mul, Units.mul_inv, globalSectionsSmul_one]

private theorem restrict_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (phi : M ⟶ N)
    (h : IsIso ((Scheme.Modules.pullback f).map phi)) : IsIso ((restrictFunctor f).map phi) := by
  let _ : IsIso ((Scheme.Modules.pullback f).map phi) := h
  let eta := restrictFunctorIsoPullback f
  let _ : IsIso (eta.hom.app M) := (eta.app M).isIso_hom
  let _ : IsIso (eta.hom.app N) := (eta.app N).isIso_hom
  exact IsIso.of_isIso_fac_right (eta.hom.naturality phi)

private def squareRight {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) {D : Scheme.{u}}
    (p : D ⟶ X.left) (q : D ⟶ Y.left) (h : p ≫ f.left = q ≫ g.left) :
    Over.mk (p ≫ X.hom) ⟶ Y :=
  Over.homMk q (by
    calc
      q ≫ Y.hom = q ≫ (g.left ≫ Z.hom) :=
        congrArg (fun t => q ≫ t) g.w.symm
      _ = (q ≫ g.left) ≫ Z.hom := (Category.assoc _ _ _).symm
      _ = (p ≫ f.left) ≫ Z.hom := congrArg (fun t => t ≫ Z.hom) h.symm
      _ = p ≫ (f.left ≫ Z.hom) := Category.assoc _ _ _
      _ = p ≫ X.hom := congrArg (fun t => p ≫ t) f.w)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "LiftEvaluation: torsor_factor"

private theorem torsor_factor {C : Type v} [Category.{w} C]
    [CartesianMonoidalCategory C] {U B H Z X : C} [MonObj H]
    (q : U ⟶ Z) (pi : H ⟶ Z) [HasPullback q pi]
    (s : U ⟶ H) (b : B ⟶ H) (e : U ⊗ B ≅ pullback q pi)
    (hf : e.hom ≫ pullback.fst q pi = fst U B)
    (hg : e.hom ≫ pullback.snd q pi = (fst U B ≫ s) * (snd U B ≫ b))
    (a : X ⟶ U) (k : X ⟶ H) (h : a ≫ q = k ≫ pi) :
    k = (a ≫ s) *
      (((pullback.lift a k h ≫ e.inv) ≫ snd U B) ≫ b) := by
  let z : X ⟶ pullback q pi := pullback.lift a k h
  let t : X ⟶ U ⊗ B := z ≫ e.inv
  have ht : t ≫ e.hom = z := by
    simp only [t, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ha : t ≫ fst U B = a := by
    calc
      t ≫ fst U B = t ≫ (e.hom ≫ pullback.fst q pi) :=
        congrArg (fun f => t ≫ f) hf.symm
      _ = (t ≫ e.hom) ≫ pullback.fst q pi := (Category.assoc _ _ _).symm
      _ = z ≫ pullback.fst q pi := congrArg (fun f => f ≫ pullback.fst q pi) ht
      _ = a := pullback.lift_fst a k h
  calc
    k = z ≫ pullback.snd q pi := (pullback.lift_snd a k h).symm
    _ = (t ≫ e.hom) ≫ pullback.snd q pi :=
      congrArg (fun f => f ≫ pullback.snd q pi) ht.symm
    _ = t ≫ (e.hom ≫ pullback.snd q pi) := Category.assoc _ _ _
    _ = t ≫ ((fst U B ≫ s) * (snd U B ≫ b)) := congrArg (fun f => t ≫ f) hg
    _ = (t ≫ (fst U B ≫ s)) * (t ≫ (snd U B ≫ b)) := MonObj.comp_mul _ _ _
    _ = ((t ≫ fst U B) ≫ s) * ((t ≫ snd U B) ≫ b) :=
      congrArg₂ (fun x y => x * y) (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
    _ = (a ≫ s) * ((t ≫ snd U B) ≫ b) :=
      congrArg (fun f => (f ≫ s) * ((t ≫ snd U B) ≫ b)) ha

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem character_unit (chi : G.characters) (X : Over (Spec (.of K)))
    (b : X ⟶ (borelVariety G).toOver) :
    IsUnit (b.left.appTop (borelCharacterSection G chi)) := by
  let r := b.left.appTop (borelCharacterSection G chi)
  let t := (b⁻¹).left.appTop (borelCharacterSection G chi)
  have h : r * t = 1 :=
    (borelCharacterSection_mul G chi X b b⁻¹).symm.trans
      ((congrArg (fun f : X ⟶ (borelVariety G).toOver =>
        f.left.appTop (borelCharacterSection G chi)) (mul_inv_cancel b)).trans
          (borelCharacterSection_one G chi X))
  exact ⟨⟨r, t, h, (mul_comm t r).trans h⟩, rfl⟩

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "LiftEvaluation: factor_evaluation_isIso"

private theorem factor_evaluation_isIso (chi : G.characters)
    (X : Over (Spec (.of K))) (g : G.points)
    (a : X ⟶ (oppositeUnipotentVariety G).toOver)
    (k : X ⟶ (reductiveVariety G).toOver) (b : X ⟶ (borelVariety G).toOver)
    (hk : k.left ≫ flagQuotient G = a.left ≫ (flagChartMorphism G g).left)
    (hfactor : k = (a ≫ flagChartMap G g) * (b ≫ borelInclusion G)) :
    IsIso (characterFrameEvaluation G chi X
      (a.left ≫ (flagChartMorphism G g).left) k hk) := by
  have hcanonical := flagCharacterPullbackIso_eval G chi g X a
  let phi := characterFrameEvaluation G chi X
    (a.left ≫ (flagChartMorphism G g).left) (a ≫ flagChartMap G g)
    ((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
      (congrArg (fun t => a.left ≫ t)
        (congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶
          (flagVariety G).toOver => f.left) (flagChartMap_quotient G g))))
  have hphi : IsIso phi := isIso_eq (g := phi) hcanonical
    (flagCharacterPullbackIso G g chi a.left).isIso_hom
  obtain ⟨unit, hunit⟩ := character_unit G chi X b
  have hscalar : IsIso (globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf)
      (b.left.appTop (borelCharacterSection G chi))) :=
    isIso_eq (congrArg (globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf)) hunit)
      (scalarIso (SheafOfModules.unit X.left.ringCatSheaf) unit).isIso_hom
  have hrule := characterFrameEvaluation_rule G chi X
    (a.left ≫ (flagChartMorphism G g).left) k (a ≫ flagChartMap G g) b hk
    ((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
      (congrArg (fun t => a.left ≫ t)
        (congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶
          (flagVariety G).toOver => f.left) (flagChartMap_quotient G g)))) hfactor
  exact isIso_eq hrule.symm (compIsIso _ _ hphi hscalar)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "LiftEvaluation: characterFrameEvaluation_isIso"

/-- A regular lift of the flag quotient trivializes its pulled-back character module. -/
theorem characterFrameEvaluation_isIso (chi : G.characters)
    (X : Over (Spec (.of K))) (m : X.left ⟶ (flagVariety G).scheme)
    (k : X ⟶ (reductiveVariety G).toOver) (hk : k.left ≫ flagQuotient G = m) :
    IsIso (characterFrameEvaluation G chi X m k hk) := by
  subst m
  let q : X ⟶ (flagVariety G).toOver := k ≫ flagQuotientMorphism G
  let cover := (flagSchemeCover G).pullback₁ q.left
  apply FrobeniusSplitting.isIso_on_open_family cover.X cover.f
    (fun x => Scheme.Cover.exists_eq cover x)
  intro g
  let V : Over (Spec (.of K)) := Over.mk (cover.f g ≫ X.hom)
  let f : V ⟶ X := Over.homMk (cover.f g) rfl
  let hcoverOpen : IsOpenImmersion (cover.f g) := inferInstance
  let _ : IsOpenImmersion f.left := hcoverOpen
  let a : V ⟶ (oppositeUnipotentVariety G).toOver :=
    squareRight q (flagChartMorphism G g) (cover.f g)
      ((flagSchemeCover G).pullbackHom q.left g)
      ((flagSchemeCover G).pullbackHom_map q.left g).symm
  have hsq : a ≫ flagChartMorphism G g = f ≫ q := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact (flagSchemeCover G).pullbackHom_map q.left g
  have hpb : a ≫ flagChartMorphism G g = (f ≫ k) ≫ flagQuotientMorphism G :=
    hsq.trans (Category.assoc f k (flagQuotientMorphism G)).symm
  let b : V ⟶ (borelVariety G).toOver :=
    (pullback.lift a (f ≫ k) hpb ≫ (flagTorsorIso G g).inv) ≫
      snd (oppositeUnipotentVariety G).toOver (borelVariety G).toOver
  have hfactor : f ≫ k = (a ≫ flagChartMap G g) * (b ≫ borelInclusion G) :=
    torsor_factor (flagChartMorphism G g) (flagQuotientMorphism G)
      (flagChartMap G g) (borelInclusion G) (flagTorsorIso G g)
      (flagTorsorIso_fst G g) (flagTorsorIso_group G g) a (f ≫ k) hpb
  have hs : (f ≫ k).left ≫ flagQuotient G =
      a.left ≫ (flagChartMorphism G g).left :=
    (congrArg (fun z : V ⟶ (flagVariety G).toOver => z.left) hpb).symm
  have hlocal := factor_evaluation_isIso G chi V g a (f ≫ k) b hs hfactor
  let _ : IsIso (characterFrameEvaluation G chi V
    (a.left ≫ (flagChartMorphism G g).left) (f ≫ k) hs) := hlocal
  have hm : a.left ≫ (flagChartMorphism G g).left =
      f.left ≫ (k.left ≫ flagQuotient G) :=
    (congrArg (fun z : V ⟶ (flagVariety G).toOver => z.left) hsq)
  have htransport := characterFrameEvaluation_congr G chi V hm (f ≫ k) hs
  let _ : IsIso ((pullbackCongr hm).hom.app (flagCharacterModule G chi)) :=
    ((pullbackCongr hm).app (flagCharacterModule G chi)).isIso_hom
  have heval : IsIso (characterFrameEvaluation G chi V
      (f.left ≫ (k.left ≫ flagQuotient G)) (f ≫ k) (hs.trans hm)) :=
    factor_isIso _ _ _
      ((pullbackCongr hm).app (flagCharacterModule G chi)).isIso_hom hlocal htransport
  let _ : IsIso (characterFrameEvaluation G chi V
    (f.left ≫ (k.left ≫ flagQuotient G)) (f ≫ k) (hs.trans hm)) := heval
  have hpull := characterFrameEvaluation_pullback G chi V X f
    (k.left ≫ flagQuotient G) k rfl
  let _ : IsIso ((pullbackComp f.left (k.left ≫ flagQuotient G)).inv.app
    (flagCharacterModule G chi)) :=
    ((pullbackComp f.left (k.left ≫ flagQuotient G)).app
      (flagCharacterModule G chi)).isIso_inv
  have hpullIso : IsIso ((Scheme.Modules.pullback f.left).map
      (characterFrameEvaluation G chi X (k.left ≫ flagQuotient G) k rfl)) :=
    middle_isIso _ _ _ _ hpull
  exact restrict_isIso f.left _ hpullIso

end SchubertGeometry.CharacterLine
