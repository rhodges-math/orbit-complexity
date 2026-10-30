import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Both polynomial coordinates of the projective section

The negative coordinate of a degree-d polynomial section is its degree-d
homogeneous reverse, including any zeros between its degree and d. The
bounded coefficient sum commutes with every coefficient-ring morphism.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u v

namespace SchubertGeometry.ProjectiveLine

open private weighted_projection
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
open private monomial_snd
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalMonomials
open private baseScalar comp_scalar spec_scalar
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialSections
open private chartSection
  from OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint

/-- Degree-d homogeneous reversal uses the chosen homogeneous degree,
including when the polynomial has smaller degree. -/
def homogeneousReverse {A : Type u} [CommRing A] (d : ℕ) (P : Polynomial A) : Polynomial A :=
  ∑ k ∈ Finset.range (d + 1), Polynomial.C (P.coeff k) * Polynomial.X ^ (d - k)

/-- Homogeneous reversal commutes with an arbitrary coefficient map. -/
theorem homogeneousReverse_map {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (d : ℕ) (P : Polynomial A) :
    Polynomial.map f (homogeneousReverse d P) = homogeneousReverse d (Polynomial.map f P) := by
  change (Polynomial.mapRingHom f)
    (∑ k ∈ Finset.range (d + 1), Polynomial.C (P.coeff k) * Polynomial.X ^ (d - k)) =
      ∑ k ∈ Finset.range (d + 1),
        Polynomial.C ((Polynomial.map f P).coeff k) * Polynomial.X ^ (d - k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  change Polynomial.map f (Polynomial.C (P.coeff k) * Polynomial.X ^ (d - k)) =
    Polynomial.C ((Polynomial.map f P).coeff k) * Polynomial.X ^ (d - k)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coeff_map]

private theorem reverse_support {A : Type u} [CommRing A] (d : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ d) :
    P.support.attach.sum
        (fun k => Polynomial.C (P.coeff k.val) * Polynomial.X ^ (d - k.val)) =
      homogeneousReverse d P := by
  classical
  have hsub : P.support ⊆ Finset.range (d + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)).trans hP))
  exact (Finset.sum_attach P.support
    (fun k => Polynomial.C (P.coeff k) * Polynomial.X ^ (d - k))).trans
      (Finset.sum_subset hsub (fun k _hk hnot => by
        have hz : P.coeff k = 0 := by
          by_contra h
          exact hnot (Polynomial.mem_support_iff.mpr h)
        rw [hz, Polynomial.C_0, zero_mul]))

private theorem mapped_reverse {A B : Type*} [CommRing A] [CommRing B]
    (f : Polynomial A →+* B) (d : ℕ) (P : Polynomial A) (hP : P.natDegree ≤ d) :
    P.support.attach.sum
        (fun k => f (Polynomial.C (P.coeff k.val) * Polynomial.X ^ (d - k.val))) =
      f (homogeneousReverse d P) := by
  rw [← map_sum]
  exact congrArg f (reverse_support d P hP)

private theorem baseScalar_right (A : Type u) [CommRing A] (a : A) :
    (projectiveLinePolynomialChart A ⟨1⟩).appTop (baseScalar A a) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.C a) :=
  (comp_scalar (projectiveLinePolynomialChart A ⟨1⟩)
    (projectiveToSpec A (ULift.{u} (Fin 2))) ((Scheme.ΓSpecIso (.of A)).inv a)).symm.trans
      ((congrArg (fun f : Spec (.of (Polynomial A)) ⟶ Spec (.of A) =>
        f.appTop ((Scheme.ΓSpecIso (.of A)).inv a))
          (projectiveLinePolynomialChart_base A ⟨1⟩)).trans (spec_scalar Polynomial.C a))

private theorem monomialScalar_right (A : Type u) [CommRing A] (d k : ℕ) (a : A) :
    (projectiveLinePolynomialChart A ⟨1⟩).appTop (baseScalar A a) *
        (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ (d - k)) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv
        (Polynomial.C a * Polynomial.X ^ (d - k)) :=
  (congrArg (fun r => r *
    (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ (d - k)))
    (baseScalar_right A a)).trans
      (map_mul (Scheme.ΓSpecIso (.of (Polynomial A))).inv.hom _ _).symm

/-- The negative-chart projection of the specified global polynomial section
has its degree-d homogeneous reverse as the polynomial coordinate. -/
theorem projectivePolynomialSection_right (A : Type u) [CommRing A] (d : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ d) :
    projectivePolynomialSection A d P hP ≫
        pullback.snd (leftRestriction A) (twistedRestriction A d) =
      chartSection A ⟨1⟩ (homogeneousReverse d P) := by
  exact weighted_projection
    (projectiveLinePolynomialChart A ⟨1⟩) P.support.attach
    _ (projectiveTransitionModule A d)
    (SheafOfModules.unit (Spec (.of (Polynomial A))).ringCatSheaf)
    (fun k => projectiveMonomialSection A d k.val
      ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp k.property)).trans hP))
    (pullback.snd (leftRestriction A) (twistedRestriction A d))
    (SheafOfModules.unitToPushforwardObjUnit
      (projectiveLinePolynomialChart A ⟨1⟩).toRingCatSheafHom)
    (fun k => baseScalar A (P.coeff k.val))
    (fun k => (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ (d - k.val)))
    (fun k => (Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (Polynomial.C (P.coeff k.val) * Polynomial.X ^ (d - k.val)))
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (homogeneousReverse d P))
    (fun k _ => monomial_snd A d k.val _)
    (fun k _ => monomialScalar_right A d k.val (P.coeff k.val))
    (mapped_reverse (Scheme.ΓSpecIso (.of (Polynomial A))).inv.hom d P hP)

end SchubertGeometry.ProjectiveLine
