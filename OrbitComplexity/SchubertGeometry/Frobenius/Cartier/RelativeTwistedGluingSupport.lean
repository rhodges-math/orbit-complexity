import OrbitComplexity.FrobeniusSplitting.Cartier.HomRestriction
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenFunctor
import OrbitComplexity.FrobeniusSplitting.Cartier.SectionTransport
import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius
import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-! # Unit-frame identities for relative Cartier gluing

The identities are proved for arbitrary scheme modules before the original
projective charts and line-source maps are substituted.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier.RelativeGlue

private abbrev unitLine (X : Scheme.{u}) := SheafOfModules.unit X.ringCatSheaf

/-- The structure unit gives the identity scalar endomorphism. -/
theorem globalSmul_one {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.globalSectionsSmul M (1 : Γ(X, ⊤)) = 𝟙 M := by
  ext U s
  change (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))) • s = s
  rw [map_one, one_smul]

/-- Morphisms on an open range are determined by their component values. -/
theorem over_hom_ext {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    {a b : M.over U ⟶ N.over U}
    (h : ∀ (V : Over U) (s : M.val.obj (op V.left)),
      (a.val.app (op V)).hom s = (b.val.app (op V)).hom s) : a = b := by
  ext V s
  exact h V.unop s

/-- An endomorphism of the restricted structure module multiplies by its unit value. -/
theorem unitOver_map_value {X : Scheme.{u}} (U : X.Opens)
    (a : (unitLine X).over U ⟶ (unitLine X).over U) (V : Over U)
    (s : Γ(X, V.left)) :
    (show Γ(X, V.left) from (a.val.app (op V)).hom s) =
      X.presheaf.map V.hom.op
        (show Γ(X, U) from (a.val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) * s := by
  let T : Over U := Over.mk (𝟙 U)
  let f : V ⟶ T := Over.homMk V.hom (Category.comp_id _)
  let av : Γ(X, V.left) →ₗ[Γ(X, V.left)] Γ(X, V.left) :=
    (a.val.app (op V)).hom
  let aTop : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (a.val.app (op T)).hom
  let r : Γ(X, U) →+* Γ(X, V.left) := (X.presheaf.map V.hom.op).hom
  have hn₀ := ConcreteCategory.congr_hom (a.val.naturality f.op) (1 : Γ(X, U))
  have hn₁ : av (r 1) = r (aTop 1) := hn₀
  have hn : av 1 = r (aTop 1) := (congrArg av r.map_one).symm.trans hn₁
  have hl : av (s * 1) = s * av 1 := av.map_smul s 1
  change av s = r (aTop 1) * s
  exact (congrArg av (mul_one s)).symm.trans
    (hl.trans ((congrArg (fun z : Γ(X, V.left) => s * z) hn).trans
      (mul_comm s (r (aTop 1)))))

/-- Precomposing a chart coefficient with a unit section gives the input action. -/
theorem precompose_trace_value (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M : X.Modules) (U : X.Opens)
    (m : unitLine X ⟶ M) (k : M.over U ⟶ (unitLine X).over U)
    (τ : localOperators (sheafFrobenius C p base) U) (V : Over U)
    (a : Γ(X, V.left)) :
    let c : Γ(X, U) :=
      ((m.over U ≫ k).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
    (τ.val.app (op V)).hom ((k.val.app (op V)).hom ((m.val.app (op V.left)).hom a)) =
      ((c • τ).val.app (op V)).hom a := by
  let c : Γ(X, U) :=
    ((m.over U ≫ k).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
  have h := congrArg (fun z : Γ(X, V.left) => (τ.val.app (op V)).hom z)
    (unitOver_map_value U (m.over U ≫ k) V a)
  exact h.trans (inputModule_apply (sheafFrobenius C p base) U c τ V a).symm

private theorem chart_app_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (U : Y.Opens) (hU : U ≤ j.opensRange) :
    Function.Injective (j.app U) := by
  let hj := j.isIso_app U hU
  exact (@asIso CommRingCat _ _ _ (j.app U) hj).commRingCatIsoToRingEquiv.injective

/-- The unit coefficient on an open range pulls back to the original chart section. -/
theorem unit_range_coefficient {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (q : unitLine Y ⟶ (Scheme.Modules.pushforward j).obj (unitLine X)) :
    let U := j.opensRange
    let c : Γ(Y, U) :=
      (((q.over U ≫ (unitOverRangeIso j).inv).val.app
        (op (Over.mk (𝟙 U))))).hom (1 : Γ(Y, U))
    j.isoOpensRange.hom.appTop (U.topIso.inv c) =
      (show Γ(X, ⊤) from (q.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) := by
  let U := j.opensRange
  let T : Over U := Over.mk (𝟙 U)
  let c : Γ(Y, U) :=
    (((q.over U ≫ (unitOverRangeIso j).inv).val.app (op T))).hom (1 : Γ(Y, U))
  let t : Γ(X, ⊤) := (q.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))
  let w : Γ(Y, U) := U.topIso.hom (j.isoOpensRange.inv.appTop t)
  have hc : j.app U c = (q.val.app (op U)).hom (1 : Γ(Y, U)) := by
    have hid : (q.over U ≫ (unitOverRangeIso j).inv) ≫
        (unitOverRangeIso j).hom = q.over U := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hv := congrArg (fun a => (a.val.app (op T)).hom (1 : Γ(Y, U))) hid
    exact (unitOverRangeIso_hom_apply j T c).symm.trans hv
  have hq : (q.val.app (op U)).hom (1 : Γ(Y, U)) =
      X.presheaf.map (j ⁻¹ᵁ U).leTop.op t := by
    have h := ConcreteCategory.congr_hom
      (q.val.naturality (homOfLE (le_top : U ≤ ⊤)).op) (1 : Γ(Y, ⊤))
    change (q.val.app (op U)).hom
        (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(Y, ⊤))) =
      X.presheaf.map (j ⁻¹ᵁ U).leTop.op t at h
    simpa only [map_one] using h
  have hw : j.app U w = X.presheaf.map (j ⁻¹ᵁ U).leTop.op t := by
    have h := openRangeWeight_apply j U j.isoOpensRange
      j.isoOpensRange_hom_ι t U le_rfl
    have hi : Y.presheaf.map (homOfLE (le_rfl : U ≤ U)).op = 𝟙 (Γ(Y, U)) :=
      Y.presheaf.map_id (op U)
    have hv : Y.presheaf.map (homOfLE (le_rfl : U ≤ U)).op w = w :=
      ConcreteCategory.congr_hom hi w
    exact (congrArg (fun z : Γ(Y, U) => j.app U z) hv).symm.trans h
  have hcw : c = w := chart_app_injective j U le_rfl (hc.trans (hq.trans hw.symm))
  change j.isoOpensRange.hom.appTop (U.topIso.inv c) = t
  rw [hcw]
  have hU := ConcreteCategory.congr_hom U.topIso.hom_inv_id
    (j.isoOpensRange.inv.appTop t)
  have he := congrArg (fun f : X ⟶ X => f.appTop) j.isoOpensRange.hom_inv_id
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at he
  exact (congrArg j.isoOpensRange.hom.appTop hU).trans
    (ConcreteCategory.congr_hom he t)

/-- A global semilinear operator is the corresponding structure-module morphism. -/
def schemeOperatorHom {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (φ : SchemeFrobeniusMap X p) :
    frobeniusRestriction C p base (unitLine X) ⟶ unitLine X where
  val :=
    { app := fun U =>
        { hom' :=
            { toFun := fun a => φ.onOpen U.unop a
              map_add' := fun a b => (φ.onOpen U.unop).map_add a b
              map_smul' := fun a b => by
                let r : Γ(X, U.unop) := a
                let s : Γ(X, U.unop) := b
                change φ.onOpen U.unop (r ^ p * s) = r * φ.onOpen U.unop s
                exact (φ.onOpen U.unop).map_pow_mul r s } }
      naturality := fun {U V} f => by
        ext a
        change φ.onOpen V.unop (X.presheaf.map f a) =
          X.presheaf.map f (φ.onOpen U.unop a)
        exact φ.restrict_comm f.unop.le a }

/-- The module morphism restricts to the same operator on every subopen. -/
theorem schemeOperatorHom_over {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (φ : SchemeFrobeniusMap X p)
    (U : X.Opens) :
    openOperatorEquiv C p base U ((schemeOperatorHom base φ).over U) = φ.restrict U := by
  apply SchemeFrobeniusMap.ext
  intro V s
  exact openOperatorEquiv_apply C p base U ((schemeOperatorHom base φ).over U) V s

/-- A unit frame cancels on overlaps of two line-source operator charts. -/
theorem cancel_frame_overlaps (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M : X.Modules)
    (m : unitLine X ⟶ M) (U V W : X.Opens) (hUW : W ≤ U) (hVW : W ≤ V)
    [IsIso (m.over U)]
    (kU : (frobeniusRestriction C p base M).over U ⟶ (unitLine X).over U)
    (kV : (frobeniusRestriction C p base M).over V ⟶ (unitLine X).over V)
    (H : frobeniusRestriction C p base (unitLine X) ⟶ unitLine X)
    (hU : ∀ (T : Over U) (a : Γ(X, T.left)),
      (kU.val.app (op T)).hom ((m.val.app (op T.left)).hom a) =
        (H.val.app (op T.left)).hom a)
    (hV : ∀ (T : Over V) (a : Γ(X, T.left)),
      (kV.val.app (op T)).hom ((m.val.app (op T.left)).hom a) =
        (H.val.app (op T.left)).hom a) :
    restrictModuleHom _ _ hUW kU = restrictModuleHom _ _ hVW kV := by
  let E := asIso (m.over U)
  apply over_hom_ext (frobeniusRestriction C p base M) (unitLine X) W
  intro T s
  have hrU := restrictModuleHom_apply (frobeniusRestriction C p base M)
    (unitLine X) hUW kU T s
  have hrV := restrictModuleHom_apply (frobeniusRestriction C p base M)
    (unitLine X) hVW kV T s
  let TU : Over U := Over.mk (T.hom ≫ homOfLE hUW)
  let TV : Over V := Over.mk (T.hom ≫ homOfLE hVW)
  let a := (E.inv.val.app (op TU)).hom s
  have ha : (m.val.app (op T.left)).hom a = s :=
    congrArg (fun q => (q.val.app (op TU)).hom s) E.inv_hom_id
  have hUv := hU TU a
  have hVv := hV TV a
  have hcU := congrArg (fun z : M.val.obj (op T.left) =>
    (kU.val.app (op TU)).hom z) ha
  have hcV := congrArg (fun z : M.val.obj (op T.left) =>
    (kV.val.app (op TV)).hom z) ha
  exact hrU.trans (hcU.symm.trans (hUv.trans (hVv.symm.trans (hcV.trans hrV.symm))))

end SchubertGeometry.ProjectiveCartier.RelativeGlue
