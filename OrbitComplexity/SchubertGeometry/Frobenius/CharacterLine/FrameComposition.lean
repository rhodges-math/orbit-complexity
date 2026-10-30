import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.NativeFrame
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Batteries.Tactic.Lint

/-! # Pullback of regular character frames -/

open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups
open AlgebraicGeometry.Scheme.Modules FrobeniusSplitting.CharacterLine

set_option autoImplicit false

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine


run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: evalRelative"

private def evalRelative {S : Scheme.{u}} (M : S.Modules) (Q : Over S)
    (i : M ⟶ relativeFunctionsObj S Q) (B : Over S) (k : B ⟶ Q) :
    (pullback B.hom).obj M ⟶ SheafOfModules.unit B.left.ringCatSheaf :=
  ((pullbackPushforwardAdjunction B.hom).homEquiv M
    (SheafOfModules.unit B.left.ringCatSheaf)).symm
      (i ≫ relativeFunctionsMap S (X := B) (Y := Q) k)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: pushforwardCongr_refl"

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    (pushforwardCongr (rfl : f = f)).hom.app M = 𝟙 ((pushforward f).obj M) := by
  apply Scheme.Modules.hom_ext
  intro V
  change M.presheaf.map (eqToHom (rfl : f ⁻¹ᵁ V = f ⁻¹ᵁ V)).op = 𝟙 _
  exact CategoryTheory.Functor.map_id M.presheaf _

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: relativeMap_comp"

private theorem relativeMap_comp {S : Scheme.{u}} (B : Over S)
    {X : Scheme.{u}} (f : X ⟶ B.left) :
    relativeFunctionsMap S (X := Over.mk (f ≫ B.hom)) (Y := B) (Over.homMk f rfl) =
      (pushforward B.hom).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (pushforwardComp f B.hom).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  let a := (pushforward B.hom).map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  let b := (pushforwardComp f B.hom).hom.app (SheafOfModules.unit X.ringCatSheaf)
  let c := (pushforwardCongr (rfl : f ≫ B.hom = f ≫ B.hom)).hom.app
    (SheafOfModules.unit X.ringCatSheaf)
  change a ≫ b ≫ c = a ≫ b
  exact (Category.assoc a b c).symm.trans
    ((congrArg (fun t => (a ≫ b) ≫ t)
      (pushforwardCongr_refl (f ≫ B.hom) (SheafOfModules.unit X.ringCatSheaf))).trans
        (Category.comp_id (a ≫ b)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: transpose_comp"

private theorem transpose_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {P : E ⥤ D}
    (a : L ⊣ R) (b : F ⊣ P) {M : C} {N : D} {O : E}
    (e : L.obj M ⟶ N) (q : F.obj N ⟶ O) :
    (a.comp b).homEquiv M O (F.map e ≫ q) =
      a.homEquiv M N e ≫ R.map (b.homEquiv N O q) := by
  have h : (a.comp b).homEquiv M O (F.map e ≫ q) =
      a.homEquiv M (P.obj O) (b.homEquiv (L.obj M) O (F.map e ≫ q)) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
  exact h.trans ((congrArg (a.homEquiv M (P.obj O))
    (b.homEquiv_naturality_left e q)).trans
      (a.homEquiv_naturality_right e (b.homEquiv N O q)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: adjunct_composite"

private theorem adjunct_composite {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (e : (pullback g).obj M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (pullbackPushforwardAdjunction (f ≫ g)).homEquiv M
        (SheafOfModules.unit X.ringCatSheaf)
        ((pullbackComp f g).inv.app M ≫ (pullback f).map e ≫ (pullbackObjUnitIso f).hom) =
      (pullbackPushforwardAdjunction g).homEquiv M
          (SheafOfModules.unit Y.ringCatSheaf) e ≫
        (pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let v : (pullback f).obj OY ⟶ OX := (pullbackObjUnitIso f).hom
  let t : (pullback f).obj ((pullback g).obj M) ⟶ OX := (pullback f).map e ≫ v
  let a := pullbackPushforwardAdjunction g
  let b := pullbackPushforwardAdjunction f
  let c := pullbackPushforwardAdjunction (f ≫ g)
  let d : (pushforward g).obj ((pushforward f).obj OX) ⟶
      (pushforward (f ≫ g)).obj OX := (pushforwardComp f g).hom.app OX
  have hm := Adjunction.homEquiv_conjugateEquiv (a.comp b) c
    (pullbackComp f g).inv t
  have hc : (conjugateEquiv (a.comp b) c (pullbackComp f g).inv).app OX = d :=
    congrArg (fun n : pushforward f ⋙ pushforward g ⟶ pushforward (f ≫ g) => n.app OX)
      (conjugateEquiv_pullbackComp_inv (f := f) (g := g))
  have hmate : c.homEquiv M OX ((pullbackComp f g).inv.app M ≫ t) =
      (a.comp b).homEquiv M OX t ≫ d :=
    hm.symm.trans (congrArg (fun n => (a.comp b).homEquiv M OX t ≫ n) hc)
  have ht := transpose_comp a b e v
  have hu : b.homEquiv OY OX v =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f
  have hpost := congrArg (fun n => n ≫ d) ht
  have hunit := congrArg (fun n => (a.homEquiv M OY e ≫ (pushforward g).map n) ≫ d) hu
  exact hmate.trans (hpost.trans (hunit.trans
    (Category.assoc (a.homEquiv M OY e)
      ((pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) d)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: evalRelative_comp"

private theorem evalRelative_comp {S : Scheme.{u}} (M : S.Modules) (Q : Over S)
    (i : M ⟶ relativeFunctionsObj S Q) (B : Over S) (k : B ⟶ Q)
    {X : Scheme.{u}} (f : X ⟶ B.left) :
    (pullbackComp f B.hom).inv.app M ≫
        (pullback f).map (evalRelative M Q i B k) ≫ (pullbackObjUnitIso f).hom =
      evalRelative M Q i (Over.mk (f ≫ B.hom)) ((Over.homMk f rfl) ≫ k) := by
  let A : Over S := Over.mk (f ≫ B.hom)
  let a : A ⟶ B := Over.homMk f rfl
  let RB : S.Modules := relativeFunctionsObj S B
  let RA : S.Modules := relativeFunctionsObj S A
  let r : M ⟶ RB := i ≫ relativeFunctionsMap S (X := B) (Y := Q) k
  let v : SheafOfModules.unit B.left.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let t : RB ⟶ RA := (pushforward B.hom).map v ≫
    (pushforwardComp f B.hom).hom.app (SheafOfModules.unit X.ringCatSheaf)
  have hb : (pullbackPushforwardAdjunction B.hom).homEquiv M
      (SheafOfModules.unit B.left.ringCatSheaf) (evalRelative M Q i B k) = r :=
    Equiv.apply_symm_apply _ _
  have ha : (pullbackPushforwardAdjunction (f ≫ B.hom)).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf) (evalRelative M Q i A (a ≫ k)) =
      i ≫ relativeFunctionsMap S (X := A) (Y := Q) (a ≫ k) :=
    Equiv.apply_symm_apply _ _
  apply ((pullbackPushforwardAdjunction (f ≫ B.hom)).homEquiv M
    (SheafOfModules.unit X.ringCatSheaf)).injective
  have h0 := adjunct_composite f B.hom M (evalRelative M Q i B k)
  have h1 := congrArg (fun n : M ⟶ RB => n ≫ t) hb
  have hr : relativeFunctionsMap S (X := A) (Y := B) a = t := relativeMap_comp B f
  have h2 := congrArg (fun n : RB ⟶ RA => r ≫ n) hr.symm
  have hf : relativeFunctionsMap S (X := B) (Y := Q) k ≫
      relativeFunctionsMap S (X := A) (Y := B) a =
      relativeFunctionsMap S (X := A) (Y := Q) (a ≫ k) :=
    ((relativeFunctions S).map_comp k.op a.op).symm
  have h3 := (Category.assoc i (relativeFunctionsMap S k) (relativeFunctionsMap S a)).trans
    (congrArg (fun n => i ≫ n) hf)
  exact h0.trans (h1.trans (h2.trans (h3.trans ha.symm)))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: characterFrameEvaluation_pullback"

/-- Evaluation of the original character module commutes with regular change of frame base. -/
theorem characterFrameEvaluation_pullback (chi : G.characters)
    (X Y : Over (Spec (.of K))) (f : X ⟶ Y) (m : Y.left ⟶ (flagVariety G).scheme)
    (k : Y ⟶ (reductiveVariety G).toOver) (hk : k.left ≫ flagQuotient G = m) :
    (pullbackComp f.left m).inv.app (flagCharacterModule G chi) ≫
        (pullback f.left).map (characterFrameEvaluation G chi Y m k hk) ≫
        (pullbackObjUnitIso f.left).hom =
      characterFrameEvaluation G chi X (f.left ≫ m) (f ≫ k)
        ((Category.assoc f.left k.left (flagQuotient G)).trans
          (congrArg (fun t => f.left ≫ t) hk)) := by
  exact evalRelative_comp (S := (flagVariety G).scheme)
    (M := flagCharacterModule G chi) (Q := Over.mk (flagQuotient G))
    (i := flagCharacterInclusion G chi) (B := Over.mk m)
    (k := Over.homMk k.left hk) f.left

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: characterFrameEvaluation_congr"

/-- Replacing the endpoint by an equal map transports the same regular frame evaluation. -/
theorem characterFrameEvaluation_congr (chi : G.characters)
    (X : Over (Spec (.of K))) {m n : X.left ⟶ (flagVariety G).scheme} (h : m = n)
    (k : X ⟶ (reductiveVariety G).toOver) (hk : k.left ≫ flagQuotient G = m) :
    (pullbackCongr h).hom.app (flagCharacterModule G chi) ≫
        characterFrameEvaluation G chi X n k (hk.trans h) =
      characterFrameEvaluation G chi X m k hk := by
  subst n
  exact Category.id_comp _

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: frameQuotient"

private theorem frameQuotient (g : G.points) :
    (flagChartMap G g).left ≫ flagQuotient G = (flagChartMorphism G g).left :=
  congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶ (flagVariety G).toOver =>
    f.left) (flagChartMap_quotient G g)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: flagCharacterPullbackIso_eval"

/-- Every pulled-back character coframe is evaluation along its original group-valued lift. -/
theorem flagCharacterPullbackIso_eval (chi : G.characters) (g : G.points)
    (X : Over (Spec (.of K))) (a : X ⟶ (oppositeUnipotentVariety G).toOver) :
    (flagCharacterPullbackIso G g chi a.left).hom =
      characterFrameEvaluation G chi X (a.left ≫ (flagChartMorphism G g).left)
        (a ≫ flagChartMap G g)
        ((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
          (congrArg (fun t => a.left ≫ t) (frameQuotient G g))) := by
  let M := flagCharacterModule G chi
  let j := (flagChartMorphism G g).left
  have he := congrArg
    (fun t => (pullbackComp a.left j).inv.app M ≫ (pullback a.left).map t ≫
      (pullbackObjUnitIso a.left).hom) (flagCharacterFrameEvaluation G g chi)
  exact he.trans (characterFrameEvaluation_pullback G chi X
    (oppositeUnipotentVariety G).toOver a j (flagChartMap G g) (frameQuotient G g))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "FrameComposition: wordCharacterFrameIso_eval"

/-- The original word-frame isomorphism reads the canonical evaluation of the same endpoint lift. -/
theorem wordCharacterFrameIso_eval (word : List G.rootBase.support) (chi : G.characters)
    (X : Over (Spec (.of K))) (k : X.left ⟶ bsdhScheme G word) (g : G.points)
    (a : X ⟶ (oppositeUnipotentVariety G).toOver)
    (h : a.left ≫ (flagChartMorphism G g).left = k ≫ bsdhMap G word) :
    (wordCharacterFrameIso G word chi k g a.left h).hom =
      (pullbackComp k (bsdhMap G word)).hom.app (flagCharacterModule G chi) ≫
        characterFrameEvaluation G chi X (k ≫ bsdhMap G word) (a ≫ flagChartMap G g)
          (((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
            (congrArg (fun t => a.left ≫ t) (frameQuotient G g))).trans h) := by
  let M := flagCharacterModule G chi
  let l := a ≫ flagChartMap G g
  have hl : l.left ≫ flagQuotient G = a.left ≫ (flagChartMorphism G g).left :=
    (Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
      (congrArg (fun t => a.left ≫ t) (frameQuotient G g))
  have he := flagCharacterPullbackIso_eval G chi g X a
  have hc := characterFrameEvaluation_congr G chi X h.symm l (hl.trans h)
  exact congrArg
    (fun t => (pullbackComp k (bsdhMap G word)).hom.app M ≫ t)
    ((congrArg (fun t => (pullbackCongr h.symm).hom.app M ≫ t) he).trans hc)

end SchubertGeometry.CharacterLine
