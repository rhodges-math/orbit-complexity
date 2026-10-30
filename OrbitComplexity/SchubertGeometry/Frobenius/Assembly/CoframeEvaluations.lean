import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Evaluation of coframes through a commutative square

Pullback comparisons and the character evaluation are combined over arbitrary
schemes. Source module identifications are made before taking hom maps.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private comparison_base_finish comparison_export comparisonTail coframeCast endpoint_pullback
    from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames

private theorem comparison_prefix_cancel {C : Type v} [Category.{w} C]
    {U V W Z T : C} (a : V ≅ U) (b : W ≅ V) (c : W ≅ Z)
    (e : Z ⟶ T) (f : U ⟶ T)
    (h : c.hom ≫ e = b.hom ≫ a.hom ≫ f) :
    (a.symm ≪≫ b.symm ≪≫ c).hom ≫ e = f := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [h]
  simp only [Iso.inv_hom_id_assoc]

private def flagComparison {P X Y Z : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (z : Y ⟶ Z)
    (L : Z.Modules) (M : X.Modules)
    (W : (pullback q).obj ((pullback z).obj L) ≅ M) :
    (pullback ((j ≫ q) ≫ z)).obj L ≅ (pullback j).obj M :=
  ((pullbackComp (j ≫ q) z).app L).symm ≪≫
    ((pullbackComp j q).app ((pullback z).obj L)).symm ≪≫
    (pullback j).mapIso W

private theorem comparisonTail_cancel {P X Y Z : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (z : Y ⟶ Z) (L : Z.Modules) (M : X.Modules)
    (W : (pullback q).obj ((pullback z).obj L) ≅ M)
    (A : (pullback j).obj M ≅ SheafOfModules.unit P.ringCatSheaf)
    (e : (pullback ((j ≫ q) ≫ z)).obj L ⟶ SheafOfModules.unit P.ringCatSheaf)
    (h : (pullback j).map W.hom ≫ A.hom = comparisonTail j q z L rfl e) :
    (flagComparison j q z L M W).hom ≫ A.hom = e := by
  apply comparison_prefix_cancel
    ((pullbackComp (j ≫ q) z).app L)
    ((pullbackComp j q).app ((pullback z).obj L))
    ((pullback j).mapIso W)
  exact h

private def pullbackPrefix {Q Y Z : Scheme.{u}}
    (r : Q ⟶ Y) (z : Y ⟶ Z) (L : Z.Modules) :
    (pullback r).obj ((pullback z).obj L) ⟶ (pullback (r ≫ z)).obj L :=
  (pullbackComp r z).hom.app L

private theorem pullbackPrefix_heq {Q Y Z : Scheme.{u}}
    (r : Q ⟶ Y) (z : Y ⟶ Z) (L : Z.Modules) :
    HEq (pullbackPrefix r z L) ((pullbackComp r z).hom.app L) :=
  HEq.rfl

private def retargetSource {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) {N N' : C} (h : N = N') {M : D} (W : F.obj N ≅ M) :
    F.obj N' ≅ M := h ▸ W

private theorem coframe_evaluation_prefix {Q Y Z : Scheme.{u}}
    (r : Q ⟶ Y) (z : Y ⟶ Z) (L : Z.Modules) (N : Y.Modules)
    (hN : N = (pullback z).obj L)
    (E : (pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    (C : (pullback r).obj N ⟶ (pullback (r ≫ z)).obj L)
    (hC : HEq C ((pullbackComp r z).hom.app L))
    (e : (pullback (r ≫ z)).obj L ⟶ SheafOfModules.unit Q.ringCatSheaf)
    (he : E.hom = C ≫ e) :
    HEq E.hom ((pullbackComp r z).hom.app L ≫ e) := by
  subst N
  have hc : C = (pullbackComp r z).hom.app L := eq_of_heq hC
  exact heq_of_eq (he.trans (congrArg (fun t => t ≫ e) hc))

private def coframeEvaluationResult
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (χ : G.characters)
    {X Y : Scheme.{u}} (P : Over (Spec (.of K)))
    (Q : Scheme.{u}) (baseQ : Q ⟶ Spec (.of K))
    (j : P.left ⟶ X) (q : X ⟶ Y) (z : Y ⟶ (flagVariety G).scheme)
    (f : P ⟶ Over.mk baseQ) (r : Q ⟶ Y) (h : j ≫ q = f.left ≫ r)
    (N : Y.Modules) (hN : N = (pullback z).obj (CharacterLine.flagCharacterModule G χ))
    (M : X.Modules) (W : (pullback q).obj N ≅ M)
    (E : (pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    (a : Over.mk baseQ ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ flagQuotient G = r ≫ z) : Prop := by
  subst N
  exact
    (flagComparison j q z (CharacterLine.flagCharacterModule G χ) M W).hom ≫
        (comparisonCoframe j q f.left r h M
          ((pullback z).obj (CharacterLine.flagCharacterModule G χ)) W.symm E).hom =
      CharacterLine.characterFrameEvaluation G χ P ((j ≫ q) ≫ z) (f ≫ a)
        (endpoint_pullback G P (Over.mk baseQ) f r z (j ≫ q) h.symm a ha)

/-- Character evaluation of a coframe transported through a commutative square.
The word module, its pullback prefix and the original coframe are retained as
whole objects until the generic module identifications are made. -/
theorem characterCoframe_evaluation
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (χ : G.characters)
    {X Y : Scheme.{u}} (P : Over (Spec (.of K)))
    (Q : Scheme.{u}) (baseQ : Q ⟶ Spec (.of K))
    (j : P.left ⟶ X) (q : X ⟶ Y) (z : Y ⟶ (flagVariety G).scheme)
    (f : P ⟶ Over.mk baseQ) (r : Q ⟶ Y) (h : j ≫ q = f.left ≫ r)
    (N : Y.Modules) (hN : N = (pullback z).obj (CharacterLine.flagCharacterModule G χ))
    (M : X.Modules) (W : (pullback q).obj N ≅ M)
    (E : (pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    (a : Over.mk baseQ ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ flagQuotient G = r ≫ z)
    (C : (pullback r).obj N ⟶
      (pullback (r ≫ z)).obj (CharacterLine.flagCharacterModule G χ))
    (hC : HEq C ((pullbackComp r z).hom.app (CharacterLine.flagCharacterModule G χ)))
    (he : E.hom = C ≫ CharacterLine.characterFrameEvaluation G χ
      (Over.mk baseQ) (r ≫ z) a ha) :
    coframeEvaluationResult G χ P Q baseQ j q z f r h N hN M W E a ha := by
  have hR := coframe_evaluation_prefix r z (CharacterLine.flagCharacterModule G χ)
    N hN E C hC _ he
  subst N
  have hc := comparison_base_finish G χ (P := P) (Q := Over.mk baseQ)
    (X := X) (Y := Y) (N := (pullback z).obj (CharacterLine.flagCharacterModule G χ))
    f h h rfl W.symm E z rfl (e' := E.hom) HEq.rfl a ha hR
  have hf := comparison_export (Y := Y) (P := P) hc W.symm rfl
    (comparisonCoframe j q f.left r h M
      ((pullback z).obj (CharacterLine.flagCharacterModule G χ)) W.symm E) rfl
    (f ≫ a) rfl (endpoint_pullback G P (Over.mk baseQ) f r z (j ≫ q) h.symm a ha)
  exact comparisonTail_cancel j q z (CharacterLine.flagCharacterModule G χ)
    M W _ _ hf

end SchubertGeometry.RetainedCharacter
