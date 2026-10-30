import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RetainedTransverseSquares
import OrbitComplexity.FrobeniusSplitting.Compatible.ClosedSchemes
import Mathlib.RingTheory.Polynomial.Ideal

/-! # Retained transverse divisors and the same scheme splitting

A weighted formula on the coordinate ring of a transverse chart proves
compatibility of its zero section with the given scheme splitting.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

open private FrobeniusSplitting.SchemeSplitting.compatible_kernel from
  OrbitComplexity.FrobeniusSplitting.Compatible.ClosedSchemes

private theorem spec_app_zero {R Q : CommRingCat.{u}} (f : R ⟶ Q)
    (s : Γ(Spec R, ⊤)) :
    (Spec.map f).appTop.hom s = 0 ↔
      f.hom ((Scheme.ΓSpecIso R).hom.hom s) = 0 := by
  have hn := congrArg (fun k : Γ(Spec R, ⊤) ⟶ Q => k.hom s)
    (Scheme.ΓSpecIso_naturality f)
  change (Scheme.ΓSpecIso Q).hom.hom ((Spec.map f).appTop.hom s) =
    f.hom ((Scheme.ΓSpecIso R).hom.hom s) at hn
  constructor
  · intro hs
    rw [hs, map_zero] at hn
    exact hn.symm
  · intro hs
    apply (Scheme.ΓSpecIso Q).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso Q).hom.hom ((Spec.map f).appTop.hom s) =
      (Scheme.ΓSpecIso Q).hom.hom 0
    rw [map_zero]
    exact hn.trans hs

private theorem spec_kernel_compatible {R Q : CommRingCat.{u}} {p : ℕ}
    (f : R ⟶ Q) [IsClosedImmersion (Spec.map f)] (hp : 0 < p)
    (ambient : SchemeSplitting (Spec R) p) (ψ : RingSplitting R p)
    (hψ : ψ.IsCompatible (RingHom.ker f.hom))
    (hambient : ∀ a : R,
      (Scheme.ΓSpecIso R).hom.hom (ambient.onOpen ⊤ ((Scheme.ΓSpecIso R).inv.hom a)) = ψ a) :
    ambient.IsCompatible (Spec.map f).ker := by
  apply FrobeniusSplitting.SchemeSplitting.compatible_kernel ambient (Spec.map f) hp
  intro s hs
  let e : Γ(Spec R, ⊤) ≃+* R := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have hs' : e s ∈ RingHom.ker f.hom := (spec_app_zero f s).mp hs
  have hψs : f.hom (ψ (e s)) = 0 := hψ hs'
  have he : e (ambient.onOpen ⊤ s) = ψ (e s) := by
    have h := hambient (e s)
    change e (ambient.onOpen ⊤ (e.symm (e s))) = ψ (e s) at h
    simpa only [e.symm_apply_apply] using h
  apply (spec_app_zero f (ambient.onOpen ⊤ s)).mpr
  change f.hom (e (ambient.onOpen ⊤ s)) = 0
  rw [he]
  exact hψs

/-- A retained unit-square coefficient makes the transverse zero section compatible
with the given weighted scheme splitting. -/
theorem retainedPolynomial_kernel
    {S K B A : Type u} [CommRing S] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S K] [Algebra S B] [Algebra K A] [Algebra S A]
    [IsScalarTower S K A] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] A) (hi : Function.Injective (algebraMap S K))
    (P : Polynomial B) (w : Bˣ)
    (hP : Polynomial.map (tensorImageHom e).toRingHom P =
      Polynomial.C (tensorImageHom e (w : B)) * Polynomial.X ^ 2)
    {T : Type u} [CommRing T] (f : B →+* T) {p : ℕ} (hp : Odd p)
    (φ : FrobeniusLinearMap (Polynomial T) p)
    (ambient : SchemeSplitting (Spec (.of (Polynomial T))) p)
    (hambient : ∀ a : Polynomial T,
      (Scheme.ΓSpecIso (.of (Polynomial T))).hom.hom
        (ambient.onOpen ⊤ ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom a)) =
          φ ((Polynomial.map f P) ^ ((p - 1) / 2) * a)) :
    ambient.IsCompatible
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T)))).ker := by
  have hp0 : 0 < p := by
    obtain ⟨k, hk⟩ := hp
    omega
  have hn : φ ((Polynomial.map f P) ^ ((p - 1) / 2)) = 1 := by
    have h := hambient 1
    simpa only [map_one, RingSplitting.map_one, mul_one] using h.symm
  let ψ : RingSplitting (Polynomial T) p :=
    φ.toSplitting ((Polynomial.map f P) ^ ((p - 1) / 2)) hn
  have hψ : ψ.IsCompatible (RingHom.ker (Polynomial.evalRingHom (0 : T))) := by
    simpa only [Polynomial.ker_evalRingHom, Polynomial.C_0, sub_zero] using
      retainedPolynomial_compatible e hi P w hP f hp φ hn
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T)))) :=
    IsClosedImmersion.spec_of_surjective _ (fun a =>
      ⟨Polynomial.C a, Polynomial.eval_C⟩)
  exact spec_kernel_compatible
    (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T))) hp0 ambient ψ hψ hambient

end SchubertGeometry.DeterminantSection
