import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.AppendFrame
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.OverlapParameters
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Character frames on the specified append product chart -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine

open private quotient_mul from OrbitComplexity.SchubertGeometry.Frobenius.AppendFrame

private theorem tensor_action {C : Type v} [Category.{w} C]
    [CartesianMonoidalCategory C] {A B U V H F : C} [MonObj H] [ModObj H F]
    (a : A ⟶ U) (b : B ⟶ V) (r : U ⟶ H) (s : V ⟶ F) :
    (a ⊗ₘ b) ≫ ((fst U V ≫ r) • (snd U V ≫ s)) =
      (fst A B ≫ a ≫ r) • (snd A B ≫ b ≫ s) := by
  simpa only [Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc] using
    (ModObj.comp_smul (a ⊗ₘ b) (fst U V ≫ r) (snd U V ≫ s))

private theorem tensor_multiply {C : Type v} [Category.{w} C]
    [CartesianMonoidalCategory C] {A B U V H : C} [MonObj H]
    (a : A ⟶ U) (b : B ⟶ V) (r : U ⟶ H) (s : V ⟶ H) :
    (a ⊗ₘ b) ≫ ((fst U V ≫ r) * (snd U V ≫ s)) =
      (fst A B ≫ a ≫ r) * (snd A B ≫ b ≫ s) := by
  simpa only [Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc] using
    (MonObj.comp_mul (a ⊗ₘ b) (fst U V ≫ r) (snd U V ≫ s))

private theorem prefix_transition {H : Type v} [Group H] (r a b c : H)
    (h : a = b * c) : r * a = (r * b) * c :=
  (congrArg (fun x => r * x) h).trans (mul_assoc r b c).symm

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev simpleFibre (i : G.rootBase.support) :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private def fibreChart (i : G.rootBase.support) (j : Fin 2) :
    (additiveVariety K).toOver ⟶ (simpleFibre G i).toOver :=
  Fin.cases (simplePositiveChart G i) (fun _ => simpleNegativeChart G i) j

private def fibreSection (i : G.rootBase.support) (j : Fin 2) :
    (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  Fin.cases (simplePositiveSection G i) (fun _ => simpleNegativeSection G i) j

private theorem fibreSection_quotient (i : G.rootBase.support) (j : Fin 2) :
    fibreSection G i j ≫ flagQuotientMorphism G =
      fibreChart G i j ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact simplePositiveSection_quotient G i
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact simpleNegativeSection_quotient G i

private def appendLift (U : Over (Spec (.of K))) (g : G.points)
    (a : U ⟶ (oppositeUnipotentVariety G).toOver)
    (i : G.rootBase.support) (j : Fin 2) :
    U ⊗ (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  (fst U (additiveVariety K).toOver ≫ a ≫ flagChartMap G g) *
    (snd U (additiveVariety K).toOver ≫ fibreSection G i j)

private abbrev overlapParameter : Over (Spec (.of K)) :=
  (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendMatching: appendLift_transition"

private theorem appendLift_transition (U : Over (Spec (.of K))) (g : G.points)
    (a : U ⟶ (oppositeUnipotentVariety G).toOver) (i : G.rootBase.support) :
    (𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) 1) ≫
        appendLift G U g a i 0 =
      ((𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) (-1)) ≫
        appendLift G U g a i 1) *
        ((snd U (overlapParameter (K := K)) ≫ ProjectiveLine.simpleOverlapMorphism G i) ≫
          borelInclusion G) := by
  let V := overlapParameter (K := K)
  let r := a ≫ flagChartMap G g
  have h₀ := tensor_multiply (𝟙 U) (ProjectiveLine.multiplicativeParameter (K := K) 1)
    r (simplePositiveSection G i)
  have h₁ := tensor_multiply (𝟙 U) (ProjectiveLine.multiplicativeParameter (K := K) (-1))
    r (simpleNegativeSection G i)
  simp only [Category.id_comp] at h₀ h₁
  have hroot := (congrArg (fun f => snd U V ≫ f)
    (ProjectiveLine.simpleFrames_transition G i)).trans
      (MonObj.comp_mul (snd U V)
        (ProjectiveLine.multiplicativeParameter (K := K) (-1) ≫ simpleNegativeSection G i)
        (ProjectiveLine.simpleOverlapMorphism G i ≫ borelInclusion G))
  have hprefix := prefix_transition (fst U V ≫ r) _ _ _ hroot
  have hlast := congrArg (fun f =>
    ((𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) (-1)) ≫
      appendLift G U g a i 1) * f)
    (Category.assoc (snd U V) (ProjectiveLine.simpleOverlapMorphism G i)
      (borelInclusion G)).symm
  exact h₀.trans (hprefix.trans
    ((congrArg (fun f => f * (snd U V ≫
      (ProjectiveLine.simpleOverlapMorphism G i ≫ borelInclusion G))) h₁.symm).trans hlast))

section Append

variable (word : List G.rootBase.support) (i : G.rootBase.support)
  (U : Over (Spec (.of K))) (g : G.points)
  (a : U ⟶ (oppositeUnipotentVariety G).toOver)
  (c : U ⊗ (simpleFibre G i).toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])))
  (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
    pullback.snd (bsdhMap G word) (flagBundleProjection G (simpleFibre G i)) =
      (a ⊗ₘ 𝟙 (simpleFibre G i).toOver).left ≫
        flagBundleChart G (simpleFibre G i) g)

private def appendChart (j : Fin 2) :
    U ⊗ (additiveVariety K).toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])) :=
  (𝟙 U ⊗ₘ fibreChart G i j) ≫ c

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendMatching: append_endpoint"

include hend in
private theorem append_endpoint : c.left ≫ bsdhMap G (word ++ [i]) =
    ((fst U (simpleFibre G i).toOver ≫ a ≫ flagChartMap G g) •
      (snd U (simpleFibre G i).toOver ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))).left := by
  let Y := simpleFibre G i
  let j := schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  have hchart := flagBundleChart_map G Y j g
  have haction := tensor_action a (𝟙 Y.toOver) (flagChartMap G g) j
  have haction' := congrArg (fun f : U ⊗ Y.toOver ⟶ (flagVariety G).toOver => f.left) haction
  simp only [Category.id_comp] at haction'
  calc
    c.left ≫ bsdhMap G (word ++ [i]) =
        c.left ≫ ((bsdhAppendIso G word i).hom.left ≫
          pullback.snd (bsdhMap G word) (flagBundleProjection G Y) ≫
            flagBundleMap G Y j) :=
      congrArg (fun f => c.left ≫ f) (bsdhAppendIso_endpoint G word i).symm
    _ = (c.left ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G Y)) ≫
          flagBundleMap G Y j := by simp only [Category.assoc]
    _ = ((a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g) ≫
        flagBundleMap G Y j := congrArg (fun f => f ≫ flagBundleMap G Y j) hend
    _ = (a ⊗ₘ 𝟙 Y.toOver).left ≫
        ((fst (oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMap G g) •
          (snd (oppositeUnipotentVariety G).toOver Y.toOver ≫ j)).left :=
      (Category.assoc _ _ _).trans (congrArg (fun f => (a ⊗ₘ 𝟙 Y.toOver).left ≫ f) hchart)
    _ = _ := haction'

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendMatching: appendLift_endpoint"

include hend in
private theorem appendLift_endpoint (j : Fin 2) :
    (appendLift G U g a i j).left ≫ flagQuotient G =
      (appendChart G word i U c j).left ≫ bsdhMap G (word ++ [i]) := by
  let Z := (additiveVariety K).toOver
  let Y := (simpleFibre G i).toOver
  let s := fibreSection G i j
  let z := fibreChart G i j
  let r := fst U Z ≫ a ≫ flagChartMap G g
  let t := snd U Z ≫ s
  have hq := quotient_mul G r t
  have hs : t ≫ flagQuotientMorphism G =
      snd U Z ≫ z ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => snd U Z ≫ f) (fibreSection_quotient G i j))
  have hquot := hq.trans (congrArg (fun f => r • f) hs)
  have he := congrArg (fun f => (𝟙 U ⊗ₘ z).left ≫ f)
    (append_endpoint G word i U g a c hend)
  have ht := tensor_action (𝟙 U) z (a ≫ flagChartMap G g)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
  have ht' := congrArg (fun f : U ⊗ Z ⟶ (flagVariety G).toOver => f.left) ht
  simp only [Category.id_comp] at ht'
  exact (congrArg (fun f : U ⊗ Z ⟶ (flagVariety G).toOver => f.left) hquot).trans
    (ht'.symm.trans he.symm)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendMatching: appendChartCharacterFrame"

include hend in
/-- Both root charts of the specified append chart carry the coframe from their group lift. -/
def appendChartCharacterFrame (chi : G.characters) (j : Fin 2) :
    (Scheme.Modules.pullback (appendChart G word i U c j).left).obj
        (wordCharacterModule G chi (word ++ [i])) ≅
      SheafOfModules.unit (U ⊗ (additiveVariety K).toOver).left.ringCatSheaf := by
  let m := (appendChart G word i U c j).left ≫ bsdhMap G (word ++ [i])
  let k := appendLift G U g a i j
  let hk : k.left ≫ flagQuotient G = m := appendLift_endpoint G word i U g a c hend j
  let e := characterFrameEvaluation G chi (U ⊗ (additiveVariety K).toOver) m k hk
  let he : IsIso e := characterFrameEvaluation_isIso G chi
    (U ⊗ (additiveVariety K).toOver) m k hk
  exact (pullbackComp (appendChart G word i U c j).left (bsdhMap G (word ++ [i]))).app
    (flagCharacterModule G chi) ≪≫ @asIso _ _ _ _ e he

end Append


end SchubertGeometry.CharacterLine
