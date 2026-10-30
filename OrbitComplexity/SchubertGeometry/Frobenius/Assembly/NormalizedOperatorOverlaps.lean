import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedGluingSupport
import OrbitComplexity.FrobeniusSplitting.Splittings.RegularWeights
import Batteries.Tactic.Lint

/-! # Cancellation of normalized line operators on open subsets

A coframe supplies a generator on each subopen. Normalization of insertion
makes the section coefficient regular, so equality after insertion determines
the original morphisms with line source.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

namespace SchubertGeometry.ProjectiveCartier

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def framedMap {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    {p : ℕ} (f : M →+ A)
    (hf : ∀ (a : A) (m : M), f ((a ^ p) • m) = a * f m) (e : M) :
    FrobeniusLinearMap A p where
  toAddMonoidHom :=
    { toFun a := f (a • e)
      map_zero' := by rw [zero_smul, map_zero]
      map_add' a b := by rw [add_smul, map_add] }
  map_pow_mul' a b := by
    change f ((a ^ p * b) • e) = a * f (b • e)
    rw [mul_smul]
    exact hf a (b • e)

private theorem framedMap_cancel {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] {p : ℕ} (hp : 0 < p)
    (f g : M →+ A)
    (hf : ∀ (a : A) (m : M), f ((a ^ p) • m) = a * f m)
    (hg : ∀ (a : A) (m : M), g ((a ^ p) • m) = a * g m)
    (e : M) (hgen : ∀ m : M, ∃ a : A, m = a • e)
    (s : M) (hnorm : f s = 1) (heq : ∀ a : A, f (a • s) = g (a • s)) : f = g := by
  obtain ⟨q, hs⟩ := hgen s
  let φ := framedMap f hf e
  let ψ := framedMap g hg e
  have hq : φ q = 1 := by
    change f (q • e) = 1
    exact (congrArg f hs).symm.trans hnorm
  have hw : φ.weight q = ψ.weight q := by
    apply FrobeniusLinearMap.ext
    intro a
    change f ((q * a) • e) = g ((q * a) • e)
    simpa only [hs, smul_smul, mul_comm] using heq a
  have hφ : φ = ψ := FrobeniusLinearMap.weight_injective hp q
    (FrobeniusLinearMap.isRegular_of_normalized φ hp q hq) hw
  ext m
  obtain ⟨a, ha⟩ := hgen m
  have h := congrArg (fun τ : FrobeniusLinearMap A p => τ a) hφ
  change f (a • e) = g (a • e) at h
  exact (congrArg f ha).trans (h.trans (congrArg g ha).symm)

private def overAdditiveMap {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (W : X.Opens)
    (k : (frobeniusRestriction C p base L).over W ⟶ (unitModule X).over W)
    (V : Over W) : Γ(L, V.left) →+ Γ(X, V.left) :=
  { toFun m := (k.val.app (op V)).hom m
    map_zero' := (k.val.app (op V)).hom.map_zero
    map_add' := (k.val.app (op V)).hom.map_add }

private theorem overAdditiveMap_smul {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules) (W : X.Opens)
    (k : (frobeniusRestriction C p base L).over W ⟶ (unitModule X).over W)
    (V : Over W) (a : Γ(X, V.left)) (m : Γ(L, V.left)) :
    overAdditiveMap base L W k V ((a ^ p) • m) =
      a * overAdditiveMap base L W k V m := by
  have h := (k.val.app (op V)).hom.map_smul a m
  change overAdditiveMap base L W k V ((a ^ p) • m) =
    a * overAdditiveMap base L W k V m at h
  exact h

private def generatedBy {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (e m : M) : Prop := ∃ a : A, m = a • e

private theorem linear_generates {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] (u : A →ₗ[A] M) (v : M →ₗ[A] A)
    (h : ∀ m : M, u (v m) = m) (e : M) (he : u 1 = e) (m : M) :
    generatedBy (A := A) e m := by
  refine ⟨v m, (h m).symm.trans ?_⟩
  have hs : u (v m) = v m • u 1 := by
    simpa only [smul_eq_mul, mul_one] using u.map_smul (v m) (1 : A)
  exact hs.trans (congrArg (fun z : M => v m • z) he)

private theorem coframe_generates {X : Scheme.{u}} (L : X.Modules) (W : X.Opens)
    (E : L.over W ≅ (unitModule X).over W) (V : Over W)
    (e : Γ(L, V.left)) (he : (E.inv.val.app (op V)).hom (1 : Γ(X, V.left)) = e)
    (m : Γ(L, V.left)) : generatedBy (A := Γ(X, V.left)) e m := by
  let u : Γ(X, V.left) →ₗ[Γ(X, V.left)] Γ(L, V.left) := (E.inv.val.app (op V)).hom
  let v : Γ(L, V.left) →ₗ[Γ(X, V.left)] Γ(X, V.left) := (E.hom.val.app (op V)).hom
  have h : ∀ m, u (v m) = m := fun m =>
    congrArg (fun f : L.over W ⟶ L.over W => (f.val.app (op V)).hom m) E.hom_inv_id
  have leaf := linear_generates (A := Γ(X, V.left)) (M := Γ(L, V.left))
  exact leaf u v h e he m

/-- Normalized insertion of the same section cancels two morphisms with
line source on an open subset, without requiring that section to be a unit. -/
theorem normalizedOverHom_cancel {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] (hp : 0 < p) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules) (W : X.Opens)
    (E : L.over W ≅ (unitModule X).over W) (s : Γ(L, W))
    (k₁ k₂ : (frobeniusRestriction C p base L).over W ⟶ (unitModule X).over W)
    (hnorm : ∀ V : Over W,
      (k₁.val.app (op V)).hom (L.presheaf.map V.hom.op s) = (1 : Γ(X, V.left)))
    (heq : ∀ (V : Over W) (a : Γ(X, V.left)),
      (k₁.val.app (op V)).hom (a • L.presheaf.map V.hom.op s) =
        (k₂.val.app (op V)).hom (a • L.presheaf.map V.hom.op s)) : k₁ = k₂ := by
  apply RelativeGlue.over_hom_ext (frobeniusRestriction C p base L) (unitModule X) W
  intro V m
  let f := overAdditiveMap base L W k₁ V
  let g := overAdditiveMap base L W k₂ V
  let e : Γ(L, V.left) := (E.inv.val.app (op V)).hom (1 : Γ(X, V.left))
  have h := framedMap_cancel hp f g
    (overAdditiveMap_smul base L W k₁ V) (overAdditiveMap_smul base L W k₂ V)
    e (coframe_generates L W E V e rfl)
    (L.presheaf.map V.hom.op s) (hnorm V) (heq V)
  exact congrArg (fun f : Γ(L, V.left) →+ Γ(X, V.left) => f m) h

end SchubertGeometry.ProjectiveCartier
