import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedPushforward
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.TwistedPushforward
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RetainedTransverseIdeals
import OrbitComplexity.FrobeniusSplitting.Splittings.Pushforward
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization

/-! # Transverse compatibility of a descended coframed splitting

The splitting descended from the given source preserves the retained
transverse zero section when its inserted coefficient is a determinant power.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite FrobeniusSplitting
open FrobeniusSplitting.OperatorSheaf
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

open ProjectiveCartier

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem inputWeight_top {X : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (c a : Γ(X, ⊤)) :
    (φ.inputWeight c).onOpen ⊤ a = φ.onOpen ⊤ (c * a) := by
  rw [SchemeFrobeniusMap.inputWeight_apply]
  have hc : X.presheaf.map (⊤ : X.Opens).leTop.op c = c := by
    change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) c = c
    rw [X.presheaf.map_id]
    rfl
  rw [hc]

/-- The same coframed source splitting descends compatibly with a retained transverse divisor. -/
theorem coframeSplitting_transverse
    {S K B A : Type u} [CommRing S] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S K] [Algebra S B] [Algebra K A] [Algebra S A]
    [IsScalarTower S K A] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] A) (hi : Function.Injective (algebraMap S K))
    (P : Polynomial B) (w : Bˣ)
    (hP : Polynomial.map (tensorImageHom e).toRingHom P =
      Polynomial.C (tensorImageHom e (w : B)) * Polynomial.X ^ 2)
    {T C : Type u} [CommRing T] [CommRing C] (g : B →+* T)
    {p : ℕ} [ExpChar C p] (hp : Odd p)
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (U : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (m : unitModule X ⟶ L)
    (Theta : frobeniusRestriction C p base L ⟶ unitModule X)
    (f : U.toScheme ⟶ Spec (.of (Polynomial T))) [IsIso f.c]
    (σ : SchemeSplitting X p)
    (hσ : σ.toOperator = twistedSectionOperator base L Theta
      ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))))
    (hc : U.topIso.inv
      (((m.over U ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) =
        f.appTop ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom
          ((Polynomial.map g P) ^ ((p - 1) / 2)))) :
    ((σ.restrict U).pushforward f).IsCompatible
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T)))).ker := by
  let target : SchemeFrobeniusMap (Spec (.of (Polynomial T))) p :=
    (framedOpenOperator base L U E (Theta.over U)).pushforward f
  let γ : Γ(Spec (.of (Polynomial T)), ⊤) ≃+* Polynomial T :=
    (Scheme.ΓSpecIso (.of (Polynomial T))).commRingCatIsoToRingEquiv
  let φ : FrobeniusLinearMap (Polynomial T) p := (target.onOpen ⊤).transport γ
  have htarget : ((σ.restrict U).pushforward f).toOperator =
      target.inputWeight ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom
        ((Polynomial.map g P) ^ ((p - 1) / 2))) := by
    exact twistedSplitting_pushforward base L Theta m σ hσ U E f _ hc
  apply retainedPolynomial_kernel e hi P w hP g hp φ ((σ.restrict U).pushforward f)
  intro a
  have h := congrArg (fun ψ : SchemeFrobeniusMap (Spec (.of (Polynomial T))) p =>
    ψ.onOpen ⊤ ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom a)) htarget
  change ((σ.restrict U).pushforward f).onOpen ⊤ ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom a)
    =
    (target.inputWeight _).onOpen ⊤ ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom a) at h
  rw [inputWeight_top] at h
  rw [h]
  change γ (target.onOpen ⊤
    (γ.symm ((Polynomial.map g P) ^ ((p - 1) / 2)) * γ.symm a)) =
      γ (target.onOpen ⊤ (γ.symm (((Polynomial.map g P) ^ ((p - 1) / 2)) * a)))
  rw [γ.symm.map_mul]

end SchubertGeometry.DeterminantSection
