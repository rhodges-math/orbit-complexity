import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateMaps
import Batteries.Tactic.Lint

/-!
# The scalar square determined by affine coordinates

Canonical tensor evaluation gives a commutative square between the regular
functions of the two affine charts. The corresponding affine squares determine
the projection of the coordinate colimits and its Cartesian scalar square.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

noncomputable section

universe u v w

namespace FrobeniusSplitting

private theorem coordinate_node {C : Type*} [Category C]
    {A B X Y P Q P' Q' : C} (f : A ⟶ B) (lN : B ⟶ P) (lF : A ⟶ Q)
    (eN : P ≅ P') (eF : Q ≅ Q') (m : Q' ⟶ P')
    (a : B ⟶ X) (b : A ⟶ Y) (d : Y ⟶ X) (i : X ⟶ P') (j : Y ⟶ Q')
    (hN : lN ≫ eN.hom = a ≫ i) (hF : lF ≫ eF.hom = b ≫ j)
    (hsquare : f ≫ a = b ≫ d) (hprojection : d ≫ i = j ≫ m) :
    f ≫ lN = lF ≫ (eF.hom ≫ m ≫ eN.inv) := by
  apply (cancel_mono eN.hom).mp
  calc
    (f ≫ lN) ≫ eN.hom = f ≫ (a ≫ i) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => f ≫ t) hN)
    _ = (f ≫ a) ≫ i := (Category.assoc _ _ _).symm
    _ = (b ≫ d) ≫ i := congrArg (fun t => t ≫ i) hsquare
    _ = b ≫ (j ≫ m) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => b ≫ t) hprojection)
    _ = (lF ≫ eF.hom) ≫ m :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ m) hF.symm)
    _ = (lF ≫ (eF.hom ≫ m ≫ eN.inv)) ≫ eN.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem cartesian_transport {C : Type*} [Category C]
    {P Q P' Q' S T : C} (m : Q' ⟶ P') (a : Q' ⟶ T) (b : P' ⟶ S) (k : T ⟶ S)
    (h : IsPullback m a b k) (eN : P ≅ P') (eF : Q ≅ Q') (q : Q ⟶ P)
    (a' : Q ⟶ T) (b' : P ⟶ S)
    (hq : q = eF.hom ≫ m ≫ eN.inv)
    (ha : eF.hom ≫ a = a') (hb : eN.hom ≫ b = b') :
    IsPullback q a' b' k := by
  apply h.of_iso' eF eN (Iso.refl T) (Iso.refl S)
  · rw [hq]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id] using ha
  · simpa only [Iso.refl_hom, Category.comp_id] using hb
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem over_iso_w {C : Type*} [Category C] {S : C}
    (X : Over S) {Y : C} (f : Y ⟶ S) (e : X ≅ Over.mk f) :
    ((Over.forget S).mapIso e).hom ≫ f = X.hom := e.hom.w

section CoordinateCocones

variable {R K : Type u} [CommRing R] [CommRing K]
    {I : Type v} [Category.{w} I]
    (N : I ⥤ CommAlgCat.{u} R) (F : I ⥤ CommAlgCat.{u} K)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (cN : Cocone (N.op ⋙ algSpec (.of R)))
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    {YR YK : Scheme.{u}} (baseR : YR ⟶ Spec (.of R)) (baseK : YK ⟶ Spec (.of K))
    (eN : cN.pt ≅ Over.mk baseR) (eF : cF.pt ≅ Over.mk baseK) (m : YK ⟶ YR)
    (WR WK : I → Scheme.{u}) [∀ s, IsAffine (WR s)] [∀ s, IsAffine (WK s)]
    (a : ∀ s, (N ⋙ forget₂ (CommAlgCat R) CommRingCat).obj s ≅ Γ(WR s, ⊤))
    (b : ∀ s, (F ⋙ forget₂ (CommAlgCat K) CommRingCat).obj s ≅ Γ(WK s, ⊤))
    (d : ∀ s, WK s ⟶ WR s) (i : ∀ s, WR s ⟶ YR) (j : ∀ s, WK s ⟶ YK)
    (hN : ∀ s, (cN.ι.app (op s)).left ≫ eN.hom.left =
      Spec.map (a s).inv ≫ (WR s).isoSpec.inv ≫ i s)
    (hF : ∀ s, (cF.ι.app (op s)).left ≫ eF.hom.left =
      Spec.map (b s).inv ≫ (WK s).isoSpec.inv ≫ j s)
    (hcoordinate : ∀ s, (a s).hom ≫ (d s).appTop = (v.app s) ≫ (b s).hom)
    (hprojection : ∀ s, d s ≫ i s = j s ≫ m)

include hN hF hcoordinate hprojection in
/-- The prescribed coefficient projection is the geometric scalar projection
because the affine coordinate equations determine every colimit leg. -/
theorem scalarModelProjection_compare :
    scalarModelProjection N F v cN cF hcF = eF.hom.left ≫ m ≫ eN.inv.left := by
  apply scalarModelProjection_unique
  intro s
  exact coordinate_node (Spec.map (v.app s)) (cN.ι.app (op s)).left
    (cF.ι.app (op s)).left ((Over.forget (Spec (.of R))).mapIso eN)
    ((Over.forget (Spec (.of K))).mapIso eF) m
    (Spec.map (a s).inv ≫ (WR s).isoSpec.inv)
    (Spec.map (b s).inv ≫ (WK s).isoSpec.inv) (d s) (i s) (j s)
    (hN s) (hF s) (affineCoordinateSquare (a s) (b s) (v.app s) (d s) (hcoordinate s))
    (hprojection s)

include hN hF hcoordinate hprojection in
/-- The scalar projection obtained from the retained coefficient diagram has
its Cartesian square on the same two cocone points. -/
theorem scalarModelProjection_cartesian (k : Spec (.of K) ⟶ Spec (.of R))
    (h : IsPullback m baseK baseR k) :
    IsPullback (scalarModelProjection N F v cN cF hcF) cF.pt.hom cN.pt.hom k :=
  cartesian_transport m baseK baseR k h
    ((Over.forget (Spec (.of R))).mapIso eN)
    ((Over.forget (Spec (.of K))).mapIso eF)
    (scalarModelProjection N F v cN cF hcF) cF.pt.hom cN.pt.hom
    (scalarModelProjection_compare N F v cN cF hcF baseR baseK eN eF m
      WR WK a b d i j hN hF hcoordinate hprojection)
    (over_iso_w cF.pt baseK eF) (over_iso_w cN.pt baseR eN)

end CoordinateCocones

end FrobeniusSplitting
