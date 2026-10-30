import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameRule
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Frames
import Batteries.Tactic.Lint

/-! # Character frames and regular torsor evaluation -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: adjunct_left_unique"
    (← IO.getStderr).flush

private theorem adjunct_left_unique {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {H : D ⥤ C} (a : F ⊣ H) (b : F' ⊣ H)
    (M : C) (Q : D) (e : F.obj M ⟶ Q) :
    b.homEquiv M Q ((Adjunction.leftAdjointUniq a b).inv.app M ≫ e) =
      a.homEquiv M Q e := by
  let N := Adjunction.leftAdjointUniq a b
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app a b M
  calc
    _ = a.homEquiv M (F'.obj M) (N.hom.app M) ≫
        H.map (N.inv.app M ≫ e) := by
      rw [hu, Adjunction.homEquiv_unit]
    _ = a.homEquiv M Q (N.hom.app M ≫ N.inv.app M ≫ e) :=
      (a.homEquiv_naturality_right (N.hom.app M) (N.inv.app M ≫ e)).symm
    _ = _ := by rw [Iso.hom_inv_id_app_assoc]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: restrict_adjunct"
    (← IO.getStderr).flush

private theorem restrict_adjunct {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (Q : X.Modules) (e : (restrictFunctor j).obj M ⟶ Q) :
    (pullbackPushforwardAdjunction j).homEquiv M Q
        ((restrictFunctorIsoPullback j).inv.app M ≫ e) =
      (restrictAdjunction j).homEquiv M Q e :=
  adjunct_left_unique (restrictAdjunction j) (pullbackPushforwardAdjunction j) M Q e

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: section_preimage_image"
    (← IO.getStderr).flush

private theorem section_preimage_image {X P Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (q : P ⟶ Y) (s : X ⟶ P)
    (h : s ≫ q = j) (W : X.Opens) : W ≤ s ⁻¹ᵁ (q ⁻¹ᵁ (j ''ᵁ W)) := by
  change W ≤ (s ≫ q) ⁻¹ᵁ (j ''ᵁ W)
  rw [h, j.preimage_image_eq]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: sectionPushforward"
    (← IO.getStderr).flush

private def sectionPushforward {X P Y : Scheme.{u}}
    (j : X ⟶ Y) (q : P ⟶ Y) (s : X ⟶ P) (h : s ≫ q = j) :
    relativeFunctionsObj Y (Over.mk q) ⟶
      (pushforward j).obj (SheafOfModules.unit X.ringCatSheaf) :=
  relativeFunctionsMap Y (X := Over.mk j) (Y := Over.mk q) (Over.homMk s h)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: U"
    (← IO.getStderr).flush

private abbrev U := (oppositeUnipotentVariety G).scheme
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: H"
    (← IO.getStderr).flush

private abbrev H := (reductiveVariety G).scheme
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: F"
    (← IO.getStderr).flush

private abbrev F := (flagVariety G).scheme

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: frame_quotient"
    (← IO.getStderr).flush

private theorem frame_quotient (g : G.points) :
    (flagChartMap G g).left ≫ flagQuotient G = (flagChartMorphism G g).left :=
  congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶
    (flagVariety G).toOver => f.left) (flagChartMap_quotient G g)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: frameSection"
    (← IO.getStderr).flush

private def frameSection (g : G.points) :
    Over.mk (flagChartMorphism G g).left ⟶ Over.mk (flagQuotient G) :=
  Over.homMk (flagChartMap G g).left (frame_quotient G g)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: regularFrameAdjunct"
    (← IO.getStderr).flush

private theorem regularFrameAdjunct (g : G.points) :
    (restrictAdjunction (flagChartMorphism G g).left).homEquiv
        (relativeFunctionsObj (F G) (Over.mk (flagQuotient G)))
        (SheafOfModules.unit (U G).ringCatSheaf) (flagCharacterEvaluation G g) =
      relativeFunctionsMap (F G) (frameSection G g) := by
  let j := (flagChartMorphism G g).left
  let q := flagQuotient G
  let sigma := (flagChartMap G g).left
  ext V s
  change Γ(H G, q ⁻¹ᵁ V) at s
  let W := j ⁻¹ᵁ V
  have hV : q ⁻¹ᵁ (j ''ᵁ W) ≤ q ⁻¹ᵁ V :=
    q.preimage_mono (j.image_preimage_le V)
  have e : W ≤ sigma ⁻¹ᵁ (q ⁻¹ᵁ (j ''ᵁ W)) :=
    section_preimage_image j q sigma (frame_quotient G g) W
  change sigma.appLE (q ⁻¹ᵁ (j ''ᵁ W)) W e
      ((H G).presheaf.map (homOfLE hV).op s) =
    ((relativeFunctionsMap (F G) (frameSection G g)).val.app (op V)).hom s
  exact (ConcreteCategory.congr_hom
    (sigma.map_appLE e (homOfLE hV).op) s).trans
      (relativeFunctionsMap_app (F G) (frameSection G g) V s).symm

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "NativeFrame: flagCharacterFrameEvaluation"
    (← IO.getStderr).flush

/-- The character coframe evaluates along the regular section of the flag torsor. -/
theorem flagCharacterFrameEvaluation (g : G.points) (chi : G.characters) :
    (restrictFunctorIsoPullback (flagChartMorphism G g).left).inv.app
        (flagCharacterModule G chi) ≫ (flagCharacterChartIso G g chi).hom =
      characterFrameEvaluation G chi (oppositeUnipotentVariety G).toOver
        (flagChartMorphism G g).left (flagChartMap G g) (frame_quotient G g) := by
  let j : U G ⟶ F G := (flagChartMorphism G g).left
  let M : (F G).Modules := flagCharacterModule G chi
  let T : (F G).Modules := relativeFunctionsObj (F G) (Over.mk (flagQuotient G))
  let O : (U G).Modules := SheafOfModules.unit (U G).ringCatSheaf
  let R : (F G).Modules ⥤ (U G).Modules := restrictFunctor j
  let P : (F G).Modules ⥤ (U G).Modules := pullback j
  let Q : (U G).Modules ⥤ (F G).Modules := pushforward j
  let a : R ⊣ Q := restrictAdjunction j
  let b : P ⊣ Q := pullbackPushforwardAdjunction j
  let coframe : R.obj M ⟶ O := (flagCharacterChartIso G g chi).hom
  let inclusion : M ⟶ T := flagCharacterInclusion G chi
  let evaluation : R.obj T ⟶ O := flagCharacterEvaluation G g
  let sectionMap : T ⟶ Q.obj O :=
    sectionPushforward (X := U G) (P := H G) (Y := F G)
      j (flagQuotient G) (flagChartMap G g).left (frame_quotient G g)
  let nativeEvaluation : P.obj M ⟶ O :=
    characterFrameEvaluation G chi (oppositeUnipotentVariety G).toOver
      j (flagChartMap G g) (frame_quotient G g)
  have h₀ : b.homEquiv M O
        ((restrictFunctorIsoPullback j).inv.app M ≫ coframe) =
      a.homEquiv M O coframe := restrict_adjunct j M O coframe
  have h₁ : a.homEquiv M O coframe =
      a.homEquiv M O (R.map inclusion ≫ evaluation) :=
    congrArg (a.homEquiv M O) (flagCharacterChartIso_eval G g chi)
  have h₂ : a.homEquiv M O (R.map inclusion ≫ evaluation) =
      inclusion ≫ a.homEquiv T O evaluation :=
    a.homEquiv_naturality_left inclusion evaluation
  have h₃ : inclusion ≫ a.homEquiv T O evaluation = inclusion ≫ sectionMap :=
    congrArg (fun t : T ⟶ Q.obj O => inclusion ≫ t) (regularFrameAdjunct G g)
  have h₄ : inclusion ≫ sectionMap = b.homEquiv M O nativeEvaluation :=
    ((b.homEquiv M O).apply_symm_apply (inclusion ≫ sectionMap)).symm
  exact (b.homEquiv M O).injective (h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄))))

end SchubertGeometry.CharacterLine
