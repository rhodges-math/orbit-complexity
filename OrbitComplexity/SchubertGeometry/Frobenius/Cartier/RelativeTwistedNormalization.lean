import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSection
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveCovariance
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialNormalization
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalization from the leading coefficient on a projective chart -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite
open GroupActions FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry.ProjectiveCartier

attribute [local instance] MvPolynomial.gradedAlgebra

open private indices line relativeBase sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private insertedInfinity
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

open private sectionWeight chartOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator

open private naturality_of_restrict projectiveChart_schematicallyDominant
  from OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveCovariance

private theorem toSpec_one {R : Type u} [CommRing R] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) (hφ : φ 1 = 1)
    (U : (Spec (.of R)).Opens) : (φ.toSpec hp).onOpen U 1 = 1 := by
  apply Subtype.ext
  funext x
  change φ.localize x.1.asIdeal.primeCompl hp 1 = 1
  simpa only [map_one, hφ] using
    φ.localize_algebraMap (S := Localization x.1.asIdeal.primeCompl)
      x.1.asIdeal.primeCompl hp 1

private theorem one_of_chart {X S : Scheme.{u}} {p : ℕ}
    (U : X.Opens) (e : S ≅ U.toScheme)
    [IsSchemeTheoreticallyDominant (e.hom ≫ U.ι)] [QuasiCompact (e.hom ≫ U.ι)]
    (φ : SchemeFrobeniusMap X p) (σ : SchemeFrobeniusMap S p)
    (hφ : φ.restrict U = σ.pushforward e.hom)
    (hσ : ∀ V, σ.onOpen V 1 = 1) : φ.onOpen ⊤ 1 = 1 := by
  apply (e.hom ≫ U.ι).app_injective ⊤
  have h := naturality_of_restrict φ U e σ hφ ⊤ 1
  simpa only [map_one, hσ] using h.symm

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private theorem trace_weight_one (ψ : FrobeniusLinearMap A p) (P : Polynomial A)
    (hdegree : P.natDegree < p + (p - 1)) (hnorm : ψ (P.coeff (p - 1)) = 1) :
    ((polynomialTraceOfOperator (K := K) ψ).weight P) 1 = 1 := by
  rw [FrobeniusLinearMap.weight_apply, mul_one,
    polynomialTraceOfOperator_constant (K := K) ψ P hdegree, hnorm, Polynomial.C_1]

/-- The first polynomial chart normalizes the projective Cartier operator when its
trace is the constant one. -/
theorem relativeCartierOperator_one (ψ : FrobeniusLinearMap A p)
    (s : (ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))).val.obj (op ⊤))
    (P : Polynomial A) (hP : sectionWeight s (⟨0⟩ : indices.{u}) = P)
    (hdegree : P.natDegree < p + (p - 1)) (hnorm : ψ (P.coeff (p - 1)) = 1) :
    (relativeCartierOperator (K := K) ψ s).onOpen ⊤ 1 = 1 := by
  let U : (line A).Opens := chartOpen A (⟨0⟩ : indices.{u})
  let e : Spec (.of (Polynomial A)) ≅ U.toScheme := projectiveLinePolynomialIso A ⟨0⟩
  have : IsSchemeTheoreticallyDominant (e.hom ≫ U.ι) :=
    projectiveChart_schematicallyDominant A
  have : QuasiCompact (e.hom ≫ U.ι) :=
    inferInstanceAs (QuasiCompact (projectiveLinePolynomialChart A ⟨0⟩))
  have hchart := relativeCartierOperator_chart (K := K) ψ s (⟨0⟩ : indices.{u})
  rw [hP] at hchart
  exact one_of_chart U e (relativeCartierOperator (K := K) ψ s)
    (((polynomialTraceOfOperator (K := K) ψ).weight P).toSpec (expChar_pos K p))
    hchart (toSpec_one _ _ (trace_weight_one (K := K) ψ P hdegree hnorm))

private theorem one_of_eq {X : Scheme.{u}} {p : ℕ}
    (φ ψ : SchemeFrobeniusMap X p) (h : φ = ψ) (hψ : ψ.onOpen ⊤ 1 = 1) :
    φ.onOpen ⊤ 1 = 1 := by
  exact h ▸ hψ

/-- Evaluating the relative twisted Cartier morphism on a section gives a
normalized operator when its inserted section has normalized first-chart trace. -/
theorem relativeTwistedOperator_one (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p))
    (P : Polynomial A)
    (hP : sectionWeight (insertedInfinity m) (⟨0⟩ : indices.{u}) = P)
    (hdegree : P.natDegree < p + (p - 1)) (hnorm : ψ (P.coeff (p - 1)) = 1) :
    (twistedSectionOperator (relativeBase (K := K) (A := A))
      (sourceLine (A := A) (p := p)) (relativeTwistedCartierMap (K := K) ψ)
      ((m.val.app (op ⊤)).hom (1 : Γ(line A, ⊤)))).onOpen ⊤ 1 = 1 := by
  exact one_of_eq _ _ (twistedSectionOperator_relative (K := K) ψ m)
    (relativeCartierOperator_one (K := K) ψ (insertedInfinity m) P hP hdegree hnorm)

/-- Evaluating the relative Cartier morphism on a section with normalized
leading coefficient gives a splitting of the projective line. -/
def relativeTwistedSectionSplitting (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p))
    (P : Polynomial A)
    (hP : sectionWeight (insertedInfinity m) (⟨0⟩ : indices.{u}) = P)
    (hdegree : P.natDegree < p + (p - 1)) (hnorm : ψ (P.coeff (p - 1)) = 1) :
    SchemeSplitting (line A) p :=
  (twistedSectionOperator (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (relativeTwistedCartierMap (K := K) ψ)
    ((m.val.app (op ⊤)).hom (1 : Γ(line A, ⊤)))).toSplitting 1
      (relativeTwistedOperator_one (K := K) ψ m P hP hdegree hnorm)


end SchubertGeometry.ProjectiveCartier
