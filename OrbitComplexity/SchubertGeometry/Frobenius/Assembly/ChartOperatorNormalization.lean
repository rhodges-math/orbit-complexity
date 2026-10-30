import OrbitComplexity.FrobeniusSplitting.Cartier.OpenFunctor
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalization reflected from an operator chart

Normalization of the prescribed projective-node operator reflects through the
chart comparison to every component of the local structure-sheaf operator.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private imageIn from OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators

private theorem normalized_everyOpen {Y : Scheme.{u}} {p : ℕ}
    (ψ : SchemeFrobeniusMap Y p) (hψ : ψ.onOpen ⊤ 1 = 1) (V : Y.Opens) :
    ψ.onOpen V 1 = 1 := by
  have h := ψ.restrict_comm (le_top : V ≤ ⊤) (1 : Γ(Y, ⊤))
  exact (congrArg (ψ.onOpen V) ((Y.presheaf.map V.leTop.op).hom.map_one)).symm.trans
    (h.trans ((congrArg (Y.presheaf.map V.leTop.op) hψ).trans
      (Y.presheaf.map V.leTop.op).hom.map_one))

private theorem openPullback_normalized {A Y : Scheme.{u}} {p : ℕ}
    (j : A ⟶ Y) [IsOpenImmersion j] (ψ : SchemeFrobeniusMap Y p)
    (hψ : ψ.onOpen ⊤ 1 = 1) (V : A.Opens) :
    (ψ.openPullback j).onOpen V 1 = 1 := by
  apply (j.appIso V).commRingCatIsoToRingEquiv.symm.injective
  exact (ψ.openPullback_appIso j V 1).trans
    ((congrArg (ψ.onOpen (j ''ᵁ V)) (j.appIso V).inv.hom.map_one).trans
      ((normalized_everyOpen ψ hψ (j ''ᵁ V)).trans (j.appIso V).inv.hom.map_one.symm))

private theorem normalized_of_iso {A Y : Scheme.{u}} {p : ℕ}
    (e : A ≅ Y) (φ : SchemeFrobeniusMap Y p)
    (h : ∀ V, (φ.openPullback e.hom).onOpen V 1 = 1) (U : Y.Opens) :
    φ.onOpen U 1 = 1 := by
  apply (asIso (e.hom.app U)).commRingCatIsoToRingEquiv.injective
  have hn := φ.openPullback_natural e.hom U (1 : Γ(Y, U))
  exact hn.symm.trans
    ((congrArg ((φ.openPullback e.hom).onOpen (e.hom ⁻¹ᵁ U))
      (e.hom.app U).hom.map_one).trans ((h _).trans (e.hom.app U).hom.map_one.symm))

private theorem localOperator_one {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (U : X.Opens) (φ : localOperators (sheafFrobenius C p base) U)
    (h : (openOperatorEquiv C p base U φ).onOpen ⊤ 1 = 1) :
    ∀ T : Over U, (φ.val.app (op T)).hom (1 : Γ(X, T.left)) = (1 : Γ(X, T.left)) := by
  let I : Over U := imageIn U ⊤
  let Z : Over U := Over.mk (𝟙 U)
  let f : I ⟶ Z := Over.homMk I.hom
  have hI : I.left = U := U.ι_image_top
  have hf : IsIso I.hom := by
    have he : I.hom = (eqToIso hI).hom := Subsingleton.elim _ _
    rw [he]
    infer_instance
  let _ := hf
  have hIone : (φ.val.app (op I)).hom (1 : Γ(X, I.left)) = (1 : Γ(X, I.left)) :=
    (openOperatorEquiv_apply C p base U φ ⊤ 1).symm.trans h
  let r : Γ(X, U) →+* Γ(X, I.left) := (X.presheaf.map I.hom.op).hom
  have hnat₀ := ConcreteCategory.congr_hom (φ.val.naturality f.op) (1 : Γ(X, U))
  have hnat : (φ.val.app (op I)).hom (r 1) =
      r ((φ.val.app (op Z)).hom (1 : Γ(X, U))) := hnat₀
  have hZ : (φ.val.app (op Z)).hom (1 : Γ(X, U)) = (1 : Γ(X, U)) := by
    apply (asIso (X.presheaf.map I.hom.op)).commRingCatIsoToRingEquiv.injective
    exact hnat.symm.trans
      ((congrArg (fun a : Γ(X, I.left) => (φ.val.app (op I)).hom a) r.map_one).trans
        (hIone.trans r.map_one.symm))
  intro T
  let g : T ⟶ Z := Over.homMk T.hom
  let t : Γ(X, U) →+* Γ(X, T.left) := (X.presheaf.map T.hom.op).hom
  have hT₀ := ConcreteCategory.congr_hom (φ.val.naturality g.op) (1 : Γ(X, U))
  have hT : (φ.val.app (op T)).hom (t 1) =
      t ((φ.val.app (op Z)).hom (1 : Γ(X, U))) := hT₀
  exact (congrArg (fun a : Γ(X, T.left) => (φ.val.app (op T)).hom a) t.map_one).symm.trans
    (hT.trans ((congrArg t hZ).trans t.map_one))

/-- Normalization of the specified node operator implies normalization of every
local component after its chart comparison. -/
theorem localOperator_one_of_chart {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (U : X.Opens) (φ : localOperators (sheafFrobenius C p base) U)
    {A Y : Scheme.{u}} (e : A ≅ U.toScheme) (j : A ⟶ Y) [IsOpenImmersion j]
    (ψ : SchemeFrobeniusMap Y p) (hψ : ψ.onOpen ⊤ 1 = 1)
    (hchart : (openOperatorEquiv C p base U φ).openPullback e.hom = ψ.openPullback j) :
    ∀ T : Over U, (φ.val.app (op T)).hom (1 : Γ(X, T.left)) = (1 : Γ(X, T.left)) := by
  apply localOperator_one base U φ
  apply normalized_of_iso e (openOperatorEquiv C p base U φ)
  intro V
  exact (congrArg (fun z : SchemeFrobeniusMap A p => z.onOpen V (1 : Γ(A, V))) hchart).trans
    (openPullback_normalized j ψ hψ V)

end SchubertGeometry.ProjectiveCartier
