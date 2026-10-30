import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierRetainedTrace
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialIdeals

/-! # Normalized append operators and prior ideals

The retained quadratic splitting has the determinant-inserted Cartier operator.
Its operators on both standard polynomial charts are normalized and preserve
extended ideals preserved by the preceding coefficient operator.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting GroupActions

namespace SchubertGeometry.ProjectiveCartier

universe u v

open private indices line relativeBase sourceLine unitLine from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private sectionWeight chartOpen from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private quadratic_degree trace_degree quadratic_normalization polynomialSection_weight from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
open private section_one from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierRetainedTrace

private theorem normalized_scheme {X : Scheme.{u}} {q : ℕ}
    (θ : SchemeFrobeniusMap X q) (hθ : θ.onOpen ⊤ 1 = 1) :
    (θ.toSplitting 1 hθ).toOperator = θ := by
  apply SchemeFrobeniusMap.ext
  intro U a
  change (θ.toSplitting 1 hθ).onOpen U a = θ.onOpen U a
  rw [SchemeFrobeniusMap.toSplitting_apply]
  simp only [map_one, one_mul]

private theorem normalized_transfer {X : Scheme.{u}} {q : ℕ}
    (σ : SchemeSplitting X q) (θ φ : SchemeFrobeniusMap X q)
    (hθ : θ.onOpen ⊤ 1 = 1) (hσ : σ = θ.toSplitting 1 hθ) (heq : θ = φ) :
    σ.toOperator = φ := by
  subst σ
  exact (normalized_scheme θ hθ).trans heq

private theorem restricted_one {X : Scheme.{u}} {q : ℕ}
    (σ : SchemeSplitting X q) (U : X.Opens) :
    (σ.toOperator.restrict U).onOpen ⊤ 1 = 1 :=
  (σ.onOpen (U.ι ''ᵁ ⊤)).map_one

private theorem section_map_one {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    f.app U (1 : Γ(Y, U)) = 1 := by
  change (f.app U).hom 1 = 1
  exact map_one _

private theorem one_of_open_top {X : Scheme.{u}} {q : ℕ}
    (θ : SchemeFrobeniusMap X q) (U : X.Opens) (hU : U = ⊤)
    (h : θ.onOpen U 1 = 1) : θ.onOpen ⊤ 1 = 1 := by
  subst U
  exact h

private theorem polynomial_chart_one {A : Type u} [CommRing A]
    {Y : Scheme.{u}} {q : ℕ} (φ : FrobeniusLinearMap A q) (hq : 0 < q)
    (θ : SchemeFrobeniusMap Y q) (hθ : θ.onOpen ⊤ 1 = 1)
    (E : Spec (.of A) ≅ Y) (heq : θ = (φ.toSpec hq).pushforward E.hom) :
    φ 1 = 1 := by
  have hpush : ((φ.toSpec hq).pushforward E.hom).onOpen ⊤ 1 = 1 := by
    rw [← heq]
    exact hθ
  have hsource : (φ.toSpec hq).onOpen (E.hom ⁻¹ᵁ ⊤) 1 = 1 := by
    have h := SchemeFrobeniusMap.pushforward_app (φ.toSpec hq) E.hom ⊤ 1
    rw [hpush, section_map_one] at h
    exact h.symm
  have hs : (φ.toSpec hq).onOpen ⊤ 1 = 1 :=
    one_of_open_top (φ.toSpec hq) (E.hom ⁻¹ᵁ ⊤) (by simp) hsource
  have hone : StructureSheaf.toOpenₗ A A ⊤ 1 = (1 : Γ(Spec (.of A), ⊤)) :=
    section_one A ⊤
  have hc := φ.toSpec_constant hq ⊤ 1
  have hv : (φ.toSpec hq).onOpen ⊤ (StructureSheaf.toOpenₗ A A ⊤ 1) =
      (1 : Γ(Spec (.of A), ⊤)) := by
    rw [hone]
    exact hs
  exact (StructureSheaf.toOpenₗ_top_bijective (R := A) (M := A)).injective
    (hc.symm.trans (hv.trans hone.symm))

private theorem normalized_ring {A : Type u} [CommRing A] {q : ℕ}
    (φ : FrobeniusLinearMap A q) (hφ : φ 1 = 1) :
    (φ.toSplitting 1 hφ).toOperator = φ := by
  apply FrobeniusLinearMap.ext
  intro a
  change (φ.toSplitting 1 hφ) a = φ a
  rw [FrobeniusLinearMap.toSplitting_apply, one_mul]

private theorem normalized_spec {A : Type u} [CommRing A]
    {Y : Scheme.{u}} {q : ℕ} (φ : FrobeniusLinearMap A q) (hφ : φ 1 = 1)
    (hq : 0 < q) (E : Spec (.of A) ≅ Y) :
    (((φ.toSplitting 1 hφ).toOperator).toSpec hq).pushforward E.hom =
      (φ.toSpec hq).pushforward E.hom := by
  rw [normalized_ring φ hφ]

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

/-- The retained quadratic splitting is the determinant-inserted Cartier
operator on every open subset of the projective line. -/
theorem retainedQuadratic_operator {B : Type v} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p)
    (hprior : ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)) = 1) :
    let m := ProjectiveLine.projectivePolynomialSection A (p - 1)
      ((Polynomial.map r P) ^ ((p - 1) / 2)) (quadratic_degree P hP r p hp)
    (retainedQuadraticSplitting (K := K) P hP r ψ hp hprior).toOperator =
      relativeCartierOperator (K := K) ψ (insertedInfinity m) := by
  let Q := (Polynomial.map r P) ^ ((p - 1) / 2)
  let m := ProjectiveLine.projectivePolynomialSection A (p - 1) Q
    (quadratic_degree P hP r p hp)
  let θ := twistedSectionOperator (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (relativeTwistedCartierMap (K := K) ψ)
    ((m.val.app (op ⊤)).hom (1 : Γ(line A, ⊤)))
  have hθ : θ.onOpen ⊤ 1 = 1 :=
    relativeTwistedOperator_one (K := K) ψ m Q
      (polynomialSection_weight A p Q (quadratic_degree P hP r p hp))
      (trace_degree hp (quadratic_degree P hP r p hp))
      (quadratic_normalization K P hP r ψ hp hprior)
  exact normalized_transfer
    (retainedQuadraticSplitting (K := K) P hP r ψ hp hprior) θ
    (relativeCartierOperator (K := K) ψ (insertedInfinity m)) hθ rfl
    (twistedSectionOperator_relative (K := K) ψ m)

include K in
/-- On each standard chart the retained quadratic splitting is represented by a
normalized polynomial splitting preserving every extended prior ideal. -/
theorem retainedQuadratic_prior {B : Type v} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p)
    (hprior : ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)) = 1)
    (I : Ideal A) (hI : ∀ a ∈ I, ψ a ∈ I) (j : indices.{u}) :
    ∃ ρ : RingSplitting (Polynomial A) p,
      (ρ.toOperator.toSpec (expChar_pos K p)).pushforward
          (projectiveLinePolynomialIso A j).hom =
        (retainedQuadraticSplitting (K := K) P hP r ψ hp hprior).toOperator.restrict
          (chartOpen A j) ∧
      ρ.IsCompatible (I.map Polynomial.C) := by
  let m := ProjectiveLine.projectivePolynomialSection A (p - 1)
    ((Polynomial.map r P) ^ ((p - 1) / 2)) (quadratic_degree P hP r p hp)
  let σ := retainedQuadraticSplitting (K := K) P hP r ψ hp hprior
  let φ := (polynomialTraceOfOperator (K := K) ψ).weight
    (sectionWeight (insertedInfinity m) j)
  have hchart : σ.toOperator.restrict (chartOpen A j) =
      (φ.toSpec (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A j).hom := by
    have h := congrArg (fun θ : SchemeFrobeniusMap (line A) p => θ.restrict (chartOpen A j))
      (retainedQuadratic_operator (K := K) P hP r ψ hp hprior)
    exact h.trans (relativeCartierOperator_chart (K := K) ψ (insertedInfinity m) j)
  have hφ : φ 1 = 1 := polynomial_chart_one φ (expChar_pos K p)
    (σ.toOperator.restrict (chartOpen A j)) (restricted_one σ (chartOpen A j))
    (projectiveLinePolynomialIso A j) hchart
  refine ⟨φ.toSplitting 1 hφ, ?_, ?_⟩
  · exact (normalized_spec φ hφ (expChar_pos K p) (projectiveLinePolynomialIso A j)).trans
      hchart.symm
  · exact polynomialTrace_compatible_map (K := K) ψ I hI
      (sectionWeight (insertedInfinity m) j) hφ

end SchubertGeometry.ProjectiveCartier
