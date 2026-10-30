import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retained polynomial append coframes

The coframes of the original global matching line are adjusted on scalar
extensions of its fixed refinement. Their field comparisons are the
polynomial append coframes constructed from the given append charts.
-/

set_option autoImplicit false

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

section Frames

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {I : Type v}
    (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra S (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[S] M l ≃ₐ[K] A l)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (r : YK ⟶ bsdhScheme G (word ++ [i]))
    (L : Y.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])))
    (j : ∀ l, Spec (.of (M l)) ⟶ Y)
    (jK : ∀ l, Spec (.of (A l)) ⟶ YK)
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = jK l ≫ q)
    (E : ∀ l, (Scheme.Modules.pullback (j l)).obj L ≅ unitModule (Spec (.of (M l))))
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

/-- The constructed scalar-chart coframes compare with the polynomial append
coframes of the same line, with all powers of their retained units. -/
def appendCoframeStage (R : Subalgebra ℤ K) (hSR : S ≤ R) : Prop :=
  FrobeniusSplitting.RetainedCharacter.coframeAdjustmentStage S M A e
    (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    q L j jK hscalar E
    (fun l => append_frame (G := G) (word := word) (i := i) (A := A) (q := q) (r := r)
      (L := L) (EL := EL) (jK := jK) (V := V) (g := g) (a := a) (c := c)
      (hend := hend) (B := B) (p := p) (ε := ε) (k := k) (hk := hk) l) R hSR

/-- A finite affine refinement of the prescribed global line admits adjusted
scalar-chart coframes whose comparisons are the constructed polynomial append coframes. -/
theorem exists_retained_append_coframes [Finite I] (hS : S.FG)
    [∀ l, Module.Flat S (M l)] [∀ l, Algebra.FinitePresentation S (M l)] :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      appendCoframeStage G word i S M A e q r L EL j jK hscalar E
        V g a c hend B p ε k hk R hSR := by
  exact FrobeniusSplitting.RetainedCharacter.exists_retained_coframe_adjustments
    S M A e (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    q L j jK hscalar E
    (fun l => append_frame (G := G) (word := word) (i := i) (A := A) (q := q) (r := r)
      (L := L) (EL := EL) (jK := jK) (V := V) (g := g) (a := a) (c := c)
      (hend := hend) (B := B) (p := p) (ε := ε) (k := k) (hk := hk) l)
    hS (fun _ _ => rfl)

end Frames

end SchubertGeometry.RetainedCharacter
