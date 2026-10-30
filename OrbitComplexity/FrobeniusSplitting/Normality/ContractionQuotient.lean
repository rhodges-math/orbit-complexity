import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ContractionIdeal
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Descending a polynomial contraction through its specified coordinate map

A surjective coordinate map descends the polynomial family once its kernel
vanishes in Laurent coordinates. The zero endpoint is derived, rather than
assumed to factor through the closed subscheme. The coefficient map only needs
to be injective for that zero endpoint; nilpotents in the quotient are allowed.

All ring comparisons occur over arbitrary rings. The scheme equations apply
Spec only after the corresponding ring-homomorphism equation has been proved.
-/

noncomputable section

namespace FrobeniusSplitting

universe u v w

variable {K : Type u} [CommRing K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {C : Type w} [CommRing C] [Algebra K C]

/-- Descend a polynomial family through the same surjective coordinate map. -/
def polynomialDescent (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0) :
    C →ₐ[K] Polynomial C :=
  AlgHom.liftOfSurjective q hq ((Polynomial.mapAlgHom q).comp α)
    (kernel_polynomial_le q.toRingHom α.toRingHom hLaurent)

/-- The descended family has the prescribed value on every representative. -/
theorem polynomialDescent_apply (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (a : A) :
    polynomialDescent q hq α hLaurent (q a) =
      Polynomial.map q.toRingHom (α a) :=
  AlgHom.liftOfSurjective_apply q hq _ _ a

/-- The coordinate square is an equality of the original algebra maps. -/
theorem polynomialDescent_comp (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0) :
    (polynomialDescent q hq α hLaurent).comp q =
      (Polynomial.mapAlgHom q).comp α :=
  AlgHom.liftOfSurjective_comp q hq _ _

/-- The identity endpoint of a polynomial family survives descent. -/
theorem polynomialDescent_one (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (hOne : ∀ a : A, (α a).eval 1 = a) (c : C) :
    (polynomialDescent q hq α hLaurent c).eval 1 = c := by
  obtain ⟨a, rfl⟩ := hq c
  rw [polynomialDescent_apply]
  calc
    (Polynomial.map q.toRingHom (α a)).eval 1 =
        q ((α a).eval 1) := by
      simpa only [map_one, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
        (Polynomial.eval_map_apply (f := q.toRingHom) (p := α a) (1 : A))
    _ = q a := congrArg q (hOne a)

private theorem scalarOrigin_kernel (q : A →ₐ[K] C)
    (hcoeff : Function.Injective (algebraMap K C))
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (ε : A →ₐ[K] K)
    (hZero : ∀ a : A, (α a).eval 0 = algebraMap K A (ε a)) :
    RingHom.ker q.toRingHom ≤ RingHom.ker ε.toRingHom := by
  intro a ha
  have hpoly : Polynomial.map q.toRingHom (α a) = 0 :=
    kernel_polynomial_vanish q.toRingHom α.toRingHom hLaurent a
      (RingHom.mem_ker.mp ha)
  have heval : (Polynomial.map q.toRingHom (α a)).eval 0 =
      q ((α a).eval 0) := by
    simpa only [map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      (Polynomial.eval_map_apply (f := q.toRingHom) (p := α a) (0 : A))
  have h := congrArg (fun P : Polynomial C => P.eval 0) hpoly
  rw [heval, hZero, q.commutes] at h
  apply RingHom.mem_ker.mpr
  apply hcoeff
  simpa only [Polynomial.eval_zero, map_zero, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using h

/-- Derive the scalar origin on the same quotient from preservation and the
injective coefficient map. No origin on the quotient is assumed. -/
def polynomialOrigin (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (hcoeff : Function.Injective (algebraMap K C))
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (ε : A →ₐ[K] K)
    (hZero : ∀ a : A, (α a).eval 0 = algebraMap K A (ε a)) : C →ₐ[K] K :=
  AlgHom.liftOfSurjective q hq ε
    (scalarOrigin_kernel q hcoeff α hLaurent ε hZero)

/-- The derived origin agrees with the given origin on representatives. -/
theorem polynomialOrigin_apply (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (hcoeff : Function.Injective (algebraMap K C))
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (ε : A →ₐ[K] K)
    (hZero : ∀ a : A, (α a).eval 0 = algebraMap K A (ε a)) (a : A) :
    polynomialOrigin q hq hcoeff α hLaurent ε hZero (q a) = ε a :=
  AlgHom.liftOfSurjective_apply q hq ε _ a

/-- The derived origin factors the original scalar origin as an equality of maps. -/
theorem polynomialOrigin_comp (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (hcoeff : Function.Injective (algebraMap K C))
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (ε : A →ₐ[K] K)
    (hZero : ∀ a : A, (α a).eval 0 = algebraMap K A (ε a)) :
    (polynomialOrigin q hq hcoeff α hLaurent ε hZero).comp q = ε := by
  ext a
  exact polynomialOrigin_apply q hq hcoeff α hLaurent ε hZero a

/-- At zero the descended family is constant through its derived origin. -/
theorem polynomialDescent_zero (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (hcoeff : Function.Injective (algebraMap K C))
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (ε : A →ₐ[K] K)
    (hZero : ∀ a : A, (α a).eval 0 = algebraMap K A (ε a)) (c : C) :
    (polynomialDescent q hq α hLaurent c).eval 0 =
      algebraMap K C (polynomialOrigin q hq hcoeff α hLaurent ε hZero c) := by
  obtain ⟨a, rfl⟩ := hq c
  rw [polynomialDescent_apply, polynomialOrigin_apply]
  calc
    (Polynomial.map q.toRingHom (α a)).eval 0 =
        q ((α a).eval 0) := by
      simpa only [map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
        (Polynomial.eval_map_apply (f := q.toRingHom) (p := α a) (0 : A))
    _ = q (algebraMap K A (ε a)) := congrArg q (hZero a)
    _ = algebraMap K C (ε a) := q.commutes (ε a)

end FrobeniusSplitting
