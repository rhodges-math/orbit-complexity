import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedBoundary
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedProjection
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialSections
import OrbitComplexity.FrobeniusSplitting.Normality.Models.RetainedTraceReset
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalized projective splittings from retained quadratic polynomials

The coefficient equation for the prior operator is the induction hypothesis.
The projective section, its Cartier normalization, and its infinity compatibility
are constructed from the quadratic polynomial and its coefficient map.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry.ProjectiveCartier

open private indices line sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private insertedInfinity
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private sectionWeight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private chartSection chartSection_top
  from OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint

open Scheme.Modules
open private monomial_fst
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalMonomials
open private baseScalar monomialScalar supportExpansion scalar_sum
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialSections

private theorem weighted_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type v} (s : Finset I) (U M : Y.Modules) (N : X.Modules)
    (m : I → (U ⟶ M)) (k : M ⟶ (pushforward f).obj N)
    (t : U ⟶ (pushforward f).obj N)
    (a : I → Γ(Y, ⊤)) (b c : I → Γ(X, ⊤)) (z : Γ(X, ⊤))
    (hm : ∀ i ∈ s, m i ≫ k = t ≫ (pushforward f).map (globalSectionsSmul N (b i)))
    (ha : ∀ i ∈ s, f.appTop (a i) * b i = c i)
    (hs : (∑ i ∈ s, c i) = z) :
    (∑ i ∈ s, m i ≫ globalSectionsSmul M (a i)) ≫ k =
      t ≫ (pushforward f).map (globalSectionsSmul N z) := by
  classical
  rw [← hs, scalar_sum, Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (m i ≫ globalSectionsSmul M (a i)) ≫ k =
        (m i ≫ k) ≫ globalSectionsSmul ((pushforward f).obj N) (a i) := by
      rw [Category.assoc, globalSectionsSmul_naturality, ← Category.assoc]
    _ = (t ≫ (pushforward f).map (globalSectionsSmul N (b i))) ≫
        (pushforward f).map (globalSectionsSmul N (f.appTop (a i))) := by
      rw [hm i hi, ← pushforward_map_globalSectionsSmul]
    _ = t ≫ (pushforward f).map
        (globalSectionsSmul N (b i) ≫ globalSectionsSmul N (f.appTop (a i))) := by
      rw [Functor.map_comp, Category.assoc]
    _ = t ≫ (pushforward f).map (globalSectionsSmul N (c i)) := by
      rw [← globalSectionsSmul_mul, ha i hi]

private theorem mapped_support {R S : Type*} [CommRing R] [CommRing S]
    (f : Polynomial R →+* S) (P : Polynomial R) :
    (P.support.attach.sum fun k => f (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val)) =
      f P := by
  rw [← map_sum, supportExpansion]

private theorem polynomial_projection (A : Type u) [CommRing A] (d : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ d) :
    ProjectiveLine.projectivePolynomialSection A d P hP ≫
        pullback.fst (ProjectiveLine.leftRestriction A)
          (ProjectiveLine.twistedRestriction A d) =
      chartSection A ⟨0⟩ P := by
  exact weighted_projection
    (projectiveLinePolynomialChart A ⟨0⟩) P.support.attach
    _ (ProjectiveLine.projectiveTransitionModule A d)
    (SheafOfModules.unit (Spec (.of (Polynomial A))).ringCatSheaf)
    (fun k => ProjectiveLine.projectiveMonomialSection A d k.val
      ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp k.property)).trans hP))
    (pullback.fst (ProjectiveLine.leftRestriction A)
      (ProjectiveLine.twistedRestriction A d))
    (SheafOfModules.unitToPushforwardObjUnit
      (projectiveLinePolynomialChart A ⟨0⟩).toRingCatSheafHom)
    (fun k => baseScalar A (P.coeff k.val))
    (fun k => (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ k.val))
    (fun k => (Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val))
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv P)
    (fun k _ => monomial_fst A d k.val _)
    (fun k _ => monomialScalar A k.val (P.coeff k.val))
    (mapped_support (Scheme.ΓSpecIso (.of (Polynomial A))).inv.hom P)

private theorem module_top_value {X : Scheme.{u}} {M N : X.Modules}
    (f g : M ⟶ N) (h : f = g) (s : M.val.obj (op ⊤)) :
    (f.val.app (op ⊤)).hom s = (g.val.app (op ⊤)).hom s :=
  congrArg (fun k : M ⟶ N => (k.val.app (op ⊤)).hom s) h

private theorem inverse_value {R S : CommRingCat.{u}} (e : R ≅ S) (s : S) :
    e.hom (e.inv s) = s :=
  ConcreteCategory.congr_hom e.inv_hom_id s

private theorem polynomialSection_weight (A : Type u) [CommRing A] (p : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ p - 1) :
    sectionWeight (insertedInfinity
      (ProjectiveLine.projectivePolynomialSection A (p - 1) P hP))
        (⟨0⟩ : indices.{u}) = P := by
  have hprojection := polynomial_projection A (p - 1) P hP
  have hvalue := module_top_value _ _ hprojection (1 : Γ(line A, ⊤))
  have hcoordinate := hvalue.trans (chartSection_top A ⟨0⟩ P)
  exact (insertedInfinity_left
    (ProjectiveLine.projectivePolynomialSection A (p - 1) P hP)).trans
      ((congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom hcoordinate).trans
        (inverse_value (Scheme.ΓSpecIso (.of (Polynomial A))) P))

private theorem quadratic_degree {B : Type v} [CommRing B]
    {A : Type u} [CommRing A] (P : Polynomial B) (hP : P.natDegree ≤ 2)
    (r : B →+* A) (p : ℕ) (hp : Odd p) :
    ((Polynomial.map r P) ^ ((p - 1) / 2)).natDegree ≤ p - 1 := by
  have hmap : (Polynomial.map r P).natDegree ≤ 2 :=
    Polynomial.natDegree_map_le.trans hP
  have hhalf : ((p - 1) / 2) * 2 = p - 1 := by
    obtain ⟨m, hm⟩ := hp.exists_bit1
    omega
  exact (Polynomial.natDegree_pow_le_of_le ((p - 1) / 2) hmap).trans_eq hhalf

private theorem trace_degree {p n : ℕ} (hp : Odd p) (hn : n ≤ p - 1) :
    n < p + (p - 1) := by
  obtain ⟨m, hm⟩ := hp.exists_bit1
  omega

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private theorem quadratic_normalization (K : Type u) [Field K]
    [ExpChar K p] [PerfectRing K p] [Algebra K A]
    {B : Type v} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p)
    (hprior : ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)) = 1) :
    ψ (((Polynomial.map r P) ^ ((p - 1) / 2)).coeff (p - 1)) = 1 := by
  apply Polynomial.C_injective
  exact (polynomialTraceOfOperator_constant (K := K) ψ
    ((Polynomial.map r P) ^ ((p - 1) / 2))
    (trace_degree hp (quadratic_degree P hP r p hp))).symm.trans
      ((retainedFrame_power_trace (K := K) P hP r ψ hp).trans
        (congrArg (Polynomial.C : A → Polynomial A) hprior))

/-- The retained quadratic polynomial defines a projective splitting when the
prior operator normalizes its leading-coefficient power. -/
def retainedQuadraticSplitting {B : Type v} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p)
    (hprior : ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)) = 1) :
    SchemeSplitting (line A) p :=
  relativeTwistedSectionSplitting (K := K) ψ
    (ProjectiveLine.projectivePolynomialSection A (p - 1)
      ((Polynomial.map r P) ^ ((p - 1) / 2)) (quadratic_degree P hP r p hp))
    ((Polynomial.map r P) ^ ((p - 1) / 2))
    (polynomialSection_weight A p _ (quadratic_degree P hP r p hp))
    (trace_degree hp (quadratic_degree P hP r p hp))
    (quadratic_normalization (K := K) P hP r ψ hp hprior)

/-- The splitting constructed from the retained quadratic polynomial preserves
the ideal of the infinity section. -/
theorem retainedQuadratic_infinity {B : Type v} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p)
    (hprior : ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)) = 1) :
    (retainedQuadraticSplitting (K := K) P hP r ψ hp hprior).IsCompatible
      (projectiveLineSection A (⟨1⟩ : indices.{u})).ker :=
  relativeTwistedSection_infinity (K := K) ψ
    (ProjectiveLine.projectivePolynomialSection A (p - 1)
      ((Polynomial.map r P) ^ ((p - 1) / 2)) (quadratic_degree P hP r p hp))
    ((Polynomial.map r P) ^ ((p - 1) / 2))
    (polynomialSection_weight A p _ (quadratic_degree P hP r p hp))
    (trace_degree hp (quadratic_degree P hP r p hp))
    (quadratic_normalization (K := K) P hP r ψ hp hprior)

-- GAP: Applying this projective construction to a chosen arithmetic word model
-- requires the append-chart comparison for its retained line and determinant
-- section after specialization, together with agreement of the resulting Cartier
-- morphisms on chart intersections. The prior coefficient equation above is an
-- induction hypothesis; it does not furnish that comparison or global agreement.


end SchubertGeometry.ProjectiveCartier
