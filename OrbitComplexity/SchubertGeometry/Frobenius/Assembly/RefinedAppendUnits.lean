import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import Batteries.Tactic.Lint

/-! # Append frame units on a common affine refinement

The arithmetic line is kept on its prescribed scheme. Pulling its existing
coframes to a common refinement and comparing with the polynomial append
coframes produces units retained on one coefficient extension, in every power.
-/

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) := SheafOfModules.unit X.ringCatSheaf

private def frame_on_composite {X Z Y : Scheme.{u}}
    (k : X ⟶ Z) (g : Z ⟶ Y) (j : X ⟶ Y) (h : j = k ≫ g)
    (L : Y.Modules) (E : (Scheme.Modules.pullback g).obj L ≅ unitModule Z) :
    (Scheme.Modules.pullback j).obj L ≅ unitModule X :=
  (pullbackCongr h).app L ≪≫ (pullbackComp k g).symm.app L ≪≫
    (Scheme.Modules.pullback k).mapIso E ≪≫ pullbackObjUnitIso k

private def compared_append_frame {A : Type u} [CommRing A]
    {Y YK Z P : Scheme.{u}} (q : YK ⟶ Y) (r : YK ⟶ Z)
    (j : Spec (.of A) ⟶ YK) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (k : Spec (.of A) ⟶ P) (g : P ⟶ Z) (h : j ≫ r = k ≫ g)
    (E : (Scheme.Modules.pullback g).obj LK ≅ unitModule P) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback q).obj L) ≅ unitModule (Spec (.of A))
        :=
  (Scheme.Modules.pullback j).mapIso EL ≪≫ (pullbackComp j r).app LK ≪≫
    frame_on_composite k g (j ≫ r) h LK E

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

private def original_frame (l : I) :
    (Scheme.Modules.pullback (jK l)).obj ((Scheme.Modules.pullback q).obj L) ≅ unitModule (Spec (.of
        (A l))) :=
  squareFrameIso q (jK l) (j l)
    (Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)))
    (hscalar l) L (E l)

private def append_frame (l : I) :
    (Scheme.Modules.pullback (jK l)).obj ((Scheme.Modules.pullback q).obj L) ≅ unitModule (Spec (.of
        (A l))) :=
  compared_append_frame q r (jK l) L _ EL (k l)
    (projectiveLinePolynomialChart (B l) (ε l) ≫
      projectiveAppendChart G i (B l) (p l) (c l)) (hk l)
    (appendPolynomialFrame G word i (V l) (g l) (a l) (c l) (hend l) (B l) (p l) 1 (ε l))

end Frames
end SchubertGeometry.RetainedCharacter
