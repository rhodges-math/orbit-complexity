import OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorCharts

/-! # Restriction and input weights in the open-operator correspondence -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
  {X : Scheme.{u}} (base : X ⟶ Spec (.of C))

private def restrictLocal {U V : X.Opens} (h : V ≤ U)
    (φ : localOperators (sheafFrobenius C p base) U) :
    localOperators (sheafFrobenius C p base) V :=
  operatorModuleSections (sheafFrobenius C p base) V
    (((operatorModule (sheafFrobenius C p base)).val.map (homOfLE h).op).hom
      ((operatorModuleSections (sheafFrobenius C p base) U).symm φ))

/-- Restricting a local Hom section restricts its corresponding scheme operator. -/
theorem openOperatorEquiv_restrict {U V : X.Opens} (h : V ≤ U)
    (φ : localOperators (sheafFrobenius C p base) U) :
    openOperatorEquiv C p base V (restrictLocal C p base h φ) =
      (openOperatorEquiv C p base U φ).openPullback (X.homOfLE h) := by
  symm
  apply SchemeFrobeniusMap.openPullback_eq_of_commute
  intro W m
  rw [openOperatorEquiv_apply, openOperatorEquiv_apply, X.homOfLE_app]
  let A : Over U := Over.mk (homOfLE
    ((X.ι_image_homOfLE_le_ι_image h W).trans (U.ι_image_le W)))
  let B : Over U := Over.mk (homOfLE (U.ι_image_le W))
  let g : A ⟶ B := Over.homMk (homOfLE (X.ι_image_homOfLE_le_ι_image h W))
  change (φ.val.app (op A)).hom
      (X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h W)).op m) =
    X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image h W)).op
      ((φ.val.app (op B)).hom m)
  exact PresheafOfModules.naturality_apply φ.val g.op m

/-- Input multiplication corresponds to weighting by the same section on the open scheme. -/
theorem openOperatorEquiv_smul (U : X.Opens) (r : Γ(X, U))
    (φ : localOperators (sheafFrobenius C p base) U) :
    openOperatorEquiv C p base U (r • φ) =
      (openOperatorEquiv C p base U φ).inputWeight (U.topIso.inv r) := by
  ext W m
  rw [openOperatorEquiv_apply, SchemeFrobeniusMap.inputWeight_apply, openOperatorEquiv_apply]
  have hr : U.toScheme.presheaf.map W.leTop.op (U.topIso.inv r) =
      X.presheaf.map (homOfLE (U.ι_image_le W)).op r := by
    rw [Scheme.Opens.topIso_inv]
    change X.presheaf.map (U.ι.opensFunctor.map W.leTop).op
        (X.presheaf.map (eqToHom U.ι_image_top).op r) = _
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  change (φ.val.app (op (Over.mk (homOfLE (U.ι_image_le W))))).hom
      (X.presheaf.map (homOfLE (U.ι_image_le W)).op r *
        (show Γ(X, U.ι ''ᵁ W) from m)) =
    (φ.val.app (op (Over.mk (homOfLE (U.ι_image_le W))))).hom
      (U.toScheme.presheaf.map W.leTop.op (U.topIso.inv r) * m)
  rw [hr]
  rfl

end FrobeniusSplitting.OperatorSheaf
