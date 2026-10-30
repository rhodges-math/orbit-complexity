import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Append coframes from the original matching model

The coframes on a common refinement are pulled from the original matching
line's singleton coframes. Their retained adjustments compare with the
polynomial append coframes on the same global line.
-/

set_option autoImplicit false

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

section Frames

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {J : Type u}
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {I : Type v} (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra S (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[S] M l ≃ₐ[K] A l)
    {YK : Scheme.{u}} (q : YK ⟶ cN.pt.left)
    (r : YK ⟶ bsdhScheme G (word ++ [i]))
    (EL : (Scheme.Modules.pullback q).obj (FrobeniusSplitting.RetainedCharacter.matchingModule N cN
        delta 1) ≅
      (Scheme.Modules.pullback r).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])))
    (j : ∀ l, Spec (.of (M l)) ⟶ cN.pt.left)
    (jK : ∀ l, Spec (.of (A l)) ⟶ YK)
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = jK l ≫ q)
    (index : I → J)
    (small : ∀ l, Spec (.of (M l)) ⟶ Spec (.of (N.obj (singletonIndex (index l)))))
    (hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op (singletonIndex (index l)))).left)
    (V : I → Over (Spec (.of K))) (g : I → G.points)
    (a : ∀ l, V l ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ l, V l ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ l, (c l).left ≫ (bsdhAppendIso G word i).hom.left ≫
      CategoryTheory.Limits.pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a l ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ (g l))
    (B : I → CommAlgCat.{u} K)
    (p : ∀ l, (algSpec (.of K)).obj (.op (B l)) ⟶ V l)
    (ε : I → ULift.{u} (Fin 2))
    (k : ∀ l, Spec (.of (A l)) ⟶ Spec (.of (Polynomial (B l))))
    (hk : ∀ l, jK l ≫ r = k l ≫ projectiveLinePolynomialChart (B l) (ε l) ≫
      projectiveAppendChart G i (B l) (p l) (c l))

private def matchingRefinementFrame (l : I) :
    (Scheme.Modules.pullback (j l)).obj (FrobeniusSplitting.RetainedCharacter.matchingModule N cN
        delta 1) ≅
      unitModule (Spec (.of (M l))) :=
  frame_on_composite (small l) (cN.ι.app (op (singletonIndex (index l)))).left
    (j l) (hsmall l) (FrobeniusSplitting.RetainedCharacter.matchingModule N cN delta 1)
    (localCharacterTrivialization N cN hcN delta 1 hco hn
      (singletonIndex (index l)) (index l) (Finset.mem_singleton_self (index l)))

/-- The original matching line admits retained adjusted coframes comparing
with the polynomial append coframes on its given common refinement. -/
def matchingAppendCoframeStage (R : Subalgebra ℤ K) (hSR : S ≤ R) : Prop :=
  appendCoframeStage G word i S M A e q r (FrobeniusSplitting.RetainedCharacter.matchingModule N cN
      delta 1) EL
    j jK hscalar (matchingRefinementFrame S N cN hcN delta hco hn M j index small hsmall)
    V g a c hend B p ε k hk R hSR

/-- The fixed matching model and its chart maps construct the retained append
coframes without choosing a new matching line on the refinement. -/
theorem exists_matching_append_coframes [Finite I] (hS : S.FG)
    [∀ l, Module.Flat S (M l)] [∀ l, Algebra.FinitePresentation S (M l)] :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      matchingAppendCoframeStage G word i S N cN hcN delta hco hn M A e q r EL
        j jK hscalar index small hsmall V g a c hend B p ε k hk R hSR := by
  exact exists_retained_append_coframes G word i S M A e q r
    (FrobeniusSplitting.RetainedCharacter.matchingModule N cN delta 1) EL j jK hscalar
    (matchingRefinementFrame S N cN hcN delta hco hn M j index small hsmall)
    V g a c hend B p ε k hk hS

end Frames

end SchubertGeometry.RetainedCharacter
