import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RangeOperatorOverlaps
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.NormalizedOperatorOverlaps
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.OpenSectionOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.CoframeOverlaps
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenFunctor
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Gluing normalized line-source chart maps

The inserted operators are compared on the prescribed chart fibre products.
Their normalized common section cancels on image intersections, after which
module-sheaf gluing produces the raw map on the original global line.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private twistedOverMap twistedOverMap_comp_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private restrictLocal from OrbitComplexity.FrobeniusSplitting.Cartier.OpenFunctor
open private sections_ext from OrbitComplexity.FrobeniusSplitting.Splittings.OperatorGluing

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem unitHom_value {X : Scheme.{u}} (L : X.Modules)
    (m : unitModule X ⟶ L) (U : X.Opens) (V : Over U) (a : Γ(X, V.left)) :
    (m.val.app (op V.left)).hom a =
      a • L.presheaf.map V.hom.op ((m.val.app (op U)).hom (1 : Γ(X, U))) := by
  let f : Γ(X, V.left) →ₗ[Γ(X, V.left)] Γ(L, V.left) :=
    (m.val.app (op V.left)).hom
  let fU : Γ(X, U) →ₗ[Γ(X, U)] Γ(L, U) := (m.val.app (op U)).hom
  let r : Γ(X, U) →+* Γ(X, V.left) := (X.presheaf.map V.hom.op).hom
  have hn₀ := ConcreteCategory.congr_hom (m.val.naturality V.hom.op) (1 : Γ(X, U))
  have hn₁ : f (r 1) = L.presheaf.map V.hom.op (fU 1) := hn₀
  have hn : f 1 = L.presheaf.map V.hom.op (fU 1) :=
    (congrArg f r.map_one).symm.trans hn₁
  have hl : f a = a • f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul a (1 : Γ(X, V.left))
  exact hl.trans (congrArg (fun x : Γ(L, V.left) => a • x) hn)

private def insertedLocal {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (m : unitModule X ⟶ L) (U : X.Opens)
    (k : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U) :
    localOperators (sheafFrobenius C p base) U :=
  twistedOverMap base (unitModule X) L U (m.over U) ≫ k

private theorem restrictLocal_apply {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) {U V : X.Opens} (h : V ≤ U)
    (φ : localOperators (sheafFrobenius C p base) U) (W : Over V) (a : Γ(X, W.left)) :
    ((restrictLocal C p base h φ).val.app (op W)).hom a =
      (φ.val.app (op (Over.mk (W.hom ≫ homOfLE h)))).hom a := rfl

private theorem normalized_maps_agree {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] (hp : 0 < p) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules) (m : unitModule X ⟶ L)
    (U V : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (kU : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U)
    (kV : (frobeniusRestriction C p base L).over V ⟶ (unitModule X).over V)
    (hnorm : ∀ T : Over U,
      (kU.val.app (op T)).hom ((m.val.app (op T.left)).hom (1 : Γ(X, T.left))) = (1 : Γ(X, T.left)))
    (heq : (openOperatorEquiv C p base U (insertedLocal base L m U kU)).openPullback
        (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) =
      (openOperatorEquiv C p base V (insertedLocal base L m V kV)).openPullback
        (X.homOfLE (inf_le_right : U ⊓ V ≤ V))) :
    restrictModuleHom _ _ (inf_le_left : U ⊓ V ≤ U) kU =
      restrictModuleHom _ _ (inf_le_right : U ⊓ V ≤ V) kV := by
  let W := U ⊓ V
  let k₁ := restrictModuleHom (frobeniusRestriction C p base L) (unitModule X)
    (inf_le_left : W ≤ U) kU
  let k₂ := restrictModuleHom (frobeniusRestriction C p base L) (unitModule X)
    (inf_le_right : W ≤ V) kV
  let s : Γ(L, W) := (m.val.app (op W)).hom (1 : Γ(X, W))
  have hi : restrictLocal C p base (inf_le_left : W ≤ U) (insertedLocal base L m U kU) =
      restrictLocal C p base (inf_le_right : W ≤ V) (insertedLocal base L m V kV) := by
    apply (openOperatorEquiv C p base W).injective
    exact (openOperatorEquiv_restrict C p base inf_le_left _).trans
      (heq.trans (openOperatorEquiv_restrict C p base inf_le_right _).symm)
  apply normalizedOverHom_cancel hp base L W
    (restrictModuleIso L (unitModule X) inf_le_left E) s k₁ k₂
  · intro T
    have hres := restrictModuleHom_apply (frobeniusRestriction C p base L)
      (unitModule X) (inf_le_left : W ≤ U) kU T
      (L.presheaf.map T.hom.op s)
    have hs := unitHom_value L m W T (1 : Γ(X, T.left))
    have hs' : L.presheaf.map T.hom.op s =
        (m.val.app (op T.left)).hom (1 : Γ(X, T.left)) := by
      have hs₀ : (m.val.app (op T.left)).hom (1 : Γ(X, T.left)) =
          L.presheaf.map T.hom.op s := by simpa only [one_smul] using hs
      exact hs₀.symm
    exact hres.trans ((congrArg
      (fun z : Γ(L, T.left) =>
        (kU.val.app (op (Over.mk (T.hom ≫ homOfLE inf_le_left)))).hom z) hs').trans
          (hnorm (Over.mk (T.hom ≫ homOfLE inf_le_left))))
  · intro T a
    have hiT := congrArg
      (fun z : localOperators (sheafFrobenius C p base) W =>
        (z.val.app (op T)).hom a) hi
    have hU := restrictLocal_apply base (inf_le_left : W ≤ U)
      (insertedLocal base L m U kU) T a
    have hV := restrictLocal_apply base (inf_le_right : W ≤ V)
      (insertedLocal base L m V kV) T a
    have hcompU := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U
      (m.over U) kU (Over.mk (T.hom ≫ homOfLE inf_le_left)) a
    have hcompV := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) V
      (m.over V) kV (Over.mk (T.hom ≫ homOfLE inf_le_right)) a
    have hvalue := unitHom_value L m W T a
    have hraw := hcompU.symm.trans (hU.symm.trans (hiT.trans (hV.trans hcompV)))
    have hrU := restrictModuleHom_apply (frobeniusRestriction C p base L)
      (unitModule X) (inf_le_left : W ≤ U) kU T (a • L.presheaf.map T.hom.op s)
    have hrV := restrictModuleHom_apply (frobeniusRestriction C p base L)
      (unitModule X) (inf_le_right : W ≤ V) kV T (a • L.presheaf.map T.hom.op s)
    have hraw' : (kU.val.app (op (Over.mk (T.hom ≫ homOfLE inf_le_left)))).hom
        (a • L.presheaf.map T.hom.op s) =
      (kV.val.app (op (Over.mk (T.hom ≫ homOfLE inf_le_right)))).hom
        (a • L.presheaf.map T.hom.op s) := by
      exact (congrArg
        (fun z : Γ(L, T.left) =>
          (kU.val.app (op (Over.mk (T.hom ≫ homOfLE inf_le_left)))).hom z)
        hvalue).symm.trans (hraw.trans (congrArg
          (fun z : Γ(L, T.left) =>
            (kV.val.app (op (Over.mk (T.hom ≫ homOfLE inf_le_right)))).hom z) hvalue))
    exact hrU.trans (hraw'.trans hrV.symm)

/-- Normalized chart maps whose inserted operators agree on chart fibre products
glue to a raw map on the same global line. Its inserted operator restricts to the
original inserted chart operators. -/
theorem exists_normalized_chart_map {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] (hp : 0 < p) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules) (m : unitModule X ⟶ L)
    (U : X.OpenCover.{u})
    (E : ∀ i, L.over (U.f i).opensRange ≅ (unitModule X).over (U.f i).opensRange)
    (k : ∀ i, (frobeniusRestriction C p base L).over (U.f i).opensRange ⟶
      (unitModule X).over (U.f i).opensRange)
    (hnorm : ∀ i (T : Over (U.f i).opensRange),
      ((k i).val.app (op T)).hom ((m.val.app (op T.left)).hom (1 : Γ(X, T.left))) = (1 : Γ(X,
          T.left)))
    (hoverlap : ∀ i j,
      ((openOperatorEquiv C p base (U.f i).opensRange
        (insertedLocal base L m (U.f i).opensRange (k i))).openPullback
          (U.f i).isoOpensRange.hom).openPullback (pullback.fst (U.f i) (U.f j)) =
      ((openOperatorEquiv C p base (U.f j).opensRange
        (insertedLocal base L m (U.f j).opensRange (k j))).openPullback
          (U.f j).isoOpensRange.hom).openPullback (pullback.snd (U.f i) (U.f j))) :
    ∃ Θ : frobeniusRestriction C p base L ⟶ unitModule X,
      (∀ i, Θ.over (U.f i).opensRange = k i) ∧
      (∀ i, (twistedSectionOperator base L Θ
          ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).restrict (U.f i).opensRange =
        openOperatorEquiv C p base (U.f i).opensRange
          (insertedLocal base L m (U.f i).opensRange (k i))) ∧
      (twistedSectionOperator base L Θ
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).onOpen ⊤ 1 = 1 := by
  have hraw : ∀ i j,
      restrictModuleHom _ _ (inf_le_left : (U.f i).opensRange ⊓ (U.f j).opensRange ≤ _) (k i) =
        restrictModuleHom _ _ (inf_le_right : (U.f i).opensRange ⊓ (U.f j).opensRange ≤ _) (k j) :=
            by
    intro i j
    exact normalized_maps_agree hp base L m _ _ (E i) (k i) (k j) (hnorm i)
      (SchubertGeometry.rangeOperators_agree (U.f i) (U.f j) _ _ (hoverlap i j))
  have hc : TopCat.Presheaf.IsCompatible
      (SheafOfModules.linearHom (frobeniusRestriction C p base L) (unitModule X)).obj
      (fun i => (U.f i).opensRange)
      (fun i => (SheafOfModules.linearHomObjEquiv _ _ _).symm (k i)) := by
    intro i j
    apply (SheafOfModules.linearHomObjEquiv _ _ _).injective
    exact hraw i j
  obtain ⟨Θ, hΘ⟩ := glueModuleMorphisms (fun i => (U.f i).opensRange) U.iSup_opensRange
    (frobeniusRestriction C p base L) (unitModule X) k hc
  refine ⟨Θ, hΘ, ?_, ?_⟩
  · intro i
    have h := twistedSectionOperator_onOpen base L Θ m (U.f i).opensRange
    have h' := congrArg
      (fun z : (frobeniusRestriction C p base L).over (U.f i).opensRange ⟶
          (unitModule X).over (U.f i).opensRange =>
        openOperatorEquiv C p base (U.f i).opensRange
          (insertedLocal base L m (U.f i).opensRange z)) (hΘ i)
    exact h.symm.trans h'
  · let Φ := twistedSectionOperator base L Θ
      ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
    apply sections_ext (fun i => (U.f i).opensRange) U.iSup_opensRange ⊤ (Φ.onOpen ⊤ 1) 1
    intro i
    let W : X.Opens := ⊤ ⊓ (U.f i).opensRange
    let T : Over (U.f i).opensRange := Over.mk (homOfLE (inf_le_right : W ≤ _))
    have hval : (Θ.val.app (op W)).hom
        ((m.val.app (op W)).hom (1 : Γ(X, W))) = (1 : Γ(X, W)) := by
      have hr := congrArg
        (fun z : (frobeniusRestriction C p base L).over (U.f i).opensRange ⟶
            (unitModule X).over (U.f i).opensRange =>
          (z.val.app (op T)).hom ((m.val.app (op W)).hom (1 : Γ(X, W)))) (hΘ i)
      exact hr.trans (hnorm i T)
    have hs : (m.val.app (op W)).hom (1 : Γ(X, W)) =
        (1 : Γ(X, W)) • L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) :=
      unitHom_value L m ⊤ (Over.mk (homOfLE (le_top : W ≤ ⊤))) (1 : Γ(X, W))
    have hs' : (m.val.app (op W)).hom (1 : Γ(X, W)) =
        L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) := by
      let t : Γ(L, W) := L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
      have ht : (1 : Γ(X, W)) • t = t := one_smul (Γ(X, W)) t
      exact hs.trans ht
    have hv : Φ.onOpen W 1 = 1 := by
      change (Θ.val.app (op W)).hom
        ((1 : Γ(X, W)) • L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))) = (1 : Γ(X, W))
      rw [one_smul, ← hs']
      exact hval
    have hres := Φ.restrict_comm (inf_le_left : W ≤ ⊤) (1 : Γ(X, ⊤))
    have hres' : X.presheaf.map (homOfLE (inf_le_left : W ≤ ⊤)).op (Φ.onOpen ⊤ 1) =
        Φ.onOpen W 1 :=
      hres.symm.trans (congrArg (Φ.onOpen W) ((X.presheaf.map
        (homOfLE (inf_le_left : W ≤ ⊤)).op).hom.map_one))
    exact hres'.trans (hv.trans ((X.presheaf.map
      (homOfLE (inf_le_left : W ≤ ⊤)).op).hom.map_one).symm)

end SchubertGeometry.ProjectiveCartier
