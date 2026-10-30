import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
import OrbitComplexity.FrobeniusSplitting.Normality.Models.RetainedTraceReset

/-! # The retained rightmost coefficient in the original Cartier chart

The polynomial coordinate is that of the given line section. The trace reset
keeps its leading coefficient inside the prior operator, on every chart open.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting Polynomial
noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveCartier

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev indices := ULift.{u} (Fin 2)
private abbrev chartOpen (A : Type u) [CommRing A] :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule indices.{u} A)
    (MvPolynomial.X (⟨0⟩ : indices.{u}))
private abbrev sectionLine (A : Type u) [CommRing A] (p : ℕ) :=
  SchubertGeometry.ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))
private abbrev rawLeft {A : Type u} [CommRing A] {p : ℕ}
    (s : (sectionLine A p).val.obj (op ⊤)) : Polynomial A :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).hom
    (((pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s)

private theorem section_one (S : Type u) [CommRing S]
    (W : (Spec (.of S)).Opens) :
    (show Γ(Spec (.of S), W) from StructureSheaf.toOpenₗ S S W (1 : S)) = 1 := by
  exact StructureSheaf.const_one W

variable {K : Type v} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

/-- On every open of the original positive chart, the retained polynomial
section gives the prior operator applied to the retained leading power. -/
theorem relativeCartierOperator_retained_trace {B : Type w} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p)
    (s : (sectionLine A p).val.obj (op ⊤))
    (hs : rawLeft s = (Polynomial.map r P) ^ ((p - 1) / 2))
    (V : (chartOpen A).toScheme.Opens) :
    (projectiveLinePolynomialIso A (⟨0⟩ : indices.{u})).hom.app V
        (((relativeCartierOperator (K := K) ψ s).restrict (chartOpen A)).onOpen V 1) =
      StructureSheaf.toOpenₗ (Polynomial A) (Polynomial A)
        ((projectiveLinePolynomialIso A (⟨0⟩ : indices.{u})).hom ⁻¹ᵁ V)
        (C (ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)))) := by
  have hchart := relativeCartierOperator_chart (K := K) ψ s (⟨0⟩ : indices.{u})
  change (relativeCartierOperator (K := K) ψ s).restrict (chartOpen A) =
    (((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
      (expChar_pos K p)).pushforward
        (projectiveLinePolynomialIso A (⟨0⟩ : indices.{u})).hom at hchart
  have htrace := retainedFrame_power_trace (K := K) P hP r ψ hp
  have hlocal (W : (Spec (.of (Polynomial A))).Opens) :
      ((((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
        (expChar_pos K p)).onOpen W 1) =
      StructureSheaf.toOpenₗ (Polynomial A) (Polynomial A) W
        (C (ψ ((r (P.coeff 2)) ^ ((p - 1) / 2)))) := by
    have ht := FrobeniusLinearMap.toSpec_constant
      ((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s))
      (expChar_pos K p) W (1 : Polynomial A)
    have hvalue : ((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s))
        (1 : Polynomial A) = C (ψ ((r (P.coeff 2)) ^ ((p - 1) / 2))) := by
      change polynomialTraceOfOperator (K := K) ψ (rawLeft s * 1) = _
      rw [mul_one, hs]
      exact htrace
    let ι : Polynomial A → Γ(Spec (.of (Polynomial A)), W) := fun z =>
      (show Γ(Spec (.of (Polynomial A)), W) from
        StructureSheaf.toOpenₗ (Polynomial A) (Polynomial A) W z)
    have hunit : ι 1 = (1 : Γ(Spec (.of (Polynomial A)), W)) :=
      section_one (Polynomial A) W
    have ht' : ((((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
          (expChar_pos K p)).onOpen W) (ι 1) =
        ι (((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)) 1) := ht
    have hin : ((((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
          (expChar_pos K p)).onOpen W) (1 : Γ(Spec (.of (Polynomial A)), W)) =
        ((((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
          (expChar_pos K p)).onOpen W) (ι 1) :=
      congrArg (fun z : Γ(Spec (.of (Polynomial A)), W) =>
        ((((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
          (expChar_pos K p)).onOpen W) z) hunit.symm
    exact hin.trans (ht'.trans (congrArg ι hvalue))
  rw [hchart]
  have happ := SchemeFrobeniusMap.pushforward_app
    (((polynomialTraceOfOperator (K := K) ψ).weight (rawLeft s)).toSpec
      (expChar_pos K p))
    (projectiveLinePolynomialIso A (⟨0⟩ : indices.{u})).hom V 1
  simp only [map_one] at happ
  exact happ.trans (hlocal _)

end SchubertGeometry.ProjectiveCartier
