import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingTraceAgreement
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedCharts
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialIdeals
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Determinant insertion in the matching trace comparison

The polynomial weight of the retained section cancels the complete inverse
coframe and affine-Jacobian factors in the prior trace. The resulting
polynomial operators commute with the specified append coordinate maps.
Their normalization is derived from the preceding global section, and both
coefficient ideals remain compatible separately.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
namespace SchubertGeometry.RetainedCharacter
universe u

open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingPriorOperator matchingPrior_normalized
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedCharts

private theorem weighted_trace_natural {A B : Type u} [CommRing A] [CommRing B]
    {p : ℕ} (f : A →+* B) (T : Polynomial B) (c : B)
    (ρ : FrobeniusLinearMap (Polynomial A) p)
    (τ : FrobeniusLinearMap (Polynomial B) p)
    (htrace : ∀ Q, τ (C c * (Polynomial.map f Q).comp T) =
      (Polynomial.map f (ρ Q)).comp T)
    (W : Polynomial A) (V : Polynomial B)
    (hsection : V = C c * (Polynomial.map f W).comp T) (Q : Polynomial A) :
    τ.weight V ((Polynomial.map f Q).comp T) =
      (Polynomial.map f (ρ.weight W Q)).comp T := by
  simpa only [FrobeniusLinearMap.weight_apply, hsection, Polynomial.map_mul,
    Polynomial.mul_comp, mul_assoc] using htrace (W * Q)

section Comparison
variable {K R J : Type u} [Field K] [CommRing R] [Algebra K R]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)

/-- Inserting the retained section weights cancels the full inverse matching
factor and affine Jacobian, giving naturality of the polynomial operators. -/
theorem retainedWeightedTrace_refine
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t)
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ t.val)
    (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hp : 0 < p) (a : (N.obj t)ˣ) (b : N.obj t)
    (W : Polynomial (N.obj s)) (V : Polynomial (N.obj t))
    (hsection : V =
      C (((((delta t j ((leOfHom f) hj) k hk *
          Units.map (N.map f).hom.toMonoidHom d * e⁻¹) ^ n)⁻¹ :
            (N.obj t)ˣ) : N.obj t) * (↑(a⁻¹) : N.obj t) ^ (p - 1)) *
        (Polynomial.map (N.map f).hom.toRingHom W).comp (C (a : N.obj t) * X + C b))
    (Q : Polynomial (N.obj s)) :
    letI : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    letI : Algebra K (N.obj t) :=
      ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
    (polynomialTraceOfOperator (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ t
        (retainedMatchingFrameSection N cN hcN delta n hco hn t k hk e))).weight V
      ((Polynomial.map (N.map f).hom.toRingHom Q).comp (C (a : N.obj t) * X + C b)) =
    (Polynomial.map (N.map f).hom.toRingHom
      ((polynomialTraceOfOperator (K := K)
        (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
          (matchingModule N cN delta n) Θ s
          (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d))).weight W Q)).comp
        (C (a : N.obj t) * X + C b) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let : Algebra K (N.obj t) :=
    ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
  exact weighted_trace_natural (N.map f).hom.toRingHom
    (C (a : N.obj t) * X + C b) _ _ _
    (fun Q => retainedMatchingTrace_refine N cN hcN delta n hco hn
      base Θ f j hj k hk d e hp a b Q) W V hsection Q
end Comparison

section Normalization
variable {K R J : Type u} [Field K] [CommRing R] [Algebra K R]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hP : ∀ j, (P j).natDegree ≤ 2)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) *
          (delta s j hj k hk : N.obj s))
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta ((p - 1) / 2)) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr
          ((p - 1) / 2)) ⊤).hom (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

/-- The weighted traces use the composed coefficient algebra. -/
local instance weightedCoefficientAlgebra (s : {s : Finset J // s.Nonempty}) : Algebra K (N.obj s)
    :=
  ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra

private abbrev firstPolynomialOperator (j : J) :
    FrobeniusLinearMap (Polynomial (N.obj (singletonIndex j))) p :=
  (polynomialTraceOfOperator (K := K)
    (matchingPriorOperator N cN hcN delta hco hn base Θ j)).weight
      ((P j) ^ ((p - 1) / 2))

include hP hr hnorm in
private theorem firstPolynomial_one (hp : Odd p) (j : J) :
    firstPolynomialOperator N cN hcN delta hco hn P base Θ j 1 = 1 := by
  have h := retainedFrame_power_trace (K := K) (P j) (hP j)
    (RingHom.id (N.obj (singletonIndex j)))
    (matchingPriorOperator N cN hcN delta hco hn base Θ j) hp
  have hprior := matchingPrior_normalized N cN hcN delta hco hn P hr base Θ hnorm j
  have htrace : polynomialTraceOfOperator (K := K)
      (matchingPriorOperator N cN hcN delta hco hn base Θ j)
      ((P j) ^ ((p - 1) / 2)) = 1 := by
    simpa only [Polynomial.map_id, RingHom.id_apply, hprior, Polynomial.C_1] using h
  change polynomialTraceOfOperator (K := K)
    (matchingPriorOperator N cN hcN delta hco hn base Θ j)
      (((P j) ^ ((p - 1) / 2)) * 1) = 1
  exact (congrArg _ (mul_one ((P j) ^ ((p - 1) / 2)))).trans htrace

/-- The first polynomial chart carries the normalized splitting constructed
from the preceding global section and the retained quadratic determinant. -/
def retainedPolynomialSplitting (hp : Odd p) (j : J) :
    RingSplitting (Polynomial (N.obj (singletonIndex j))) p :=
  (firstPolynomialOperator N cN hcN delta hco hn P base Θ j).toSplitting 1
    (firstPolynomial_one N cN hcN delta hco hn P hP hr base Θ hnorm hp j)

/-- The constructed polynomial splitting is the determinant-weighted trace
itself, with its complete retained polynomial power. -/
theorem retainedPolynomial_operator (hp : Odd p) (j : J) :
    (retainedPolynomialSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp j).toOperator =
      firstPolynomialOperator N cN hcN delta hco hn P base Θ j := by
  apply FrobeniusLinearMap.ext
  intro Q
  exact congrArg (firstPolynomialOperator N cN hcN delta hco hn P base Θ j) (one_mul Q)

/-- Each original coefficient ideal is separately preserved by the
normalized polynomial splitting; their identification is retained as input. -/
theorem retainedPolynomial_prior (hp : Odd p) (j : J)
    (I : Ideal (N.obj (singletonIndex j)))
    (hI : ∀ a ∈ I, matchingPriorOperator N cN hcN delta hco hn base Θ j a ∈ I) :
    (retainedPolynomialSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp j).IsCompatible
      (I.map Polynomial.C) :=
  polynomialTrace_compatible_map
    (matchingPriorOperator N cN hcN delta hco hn base Θ j) I hI
    ((P j) ^ ((p - 1) / 2))
    (firstPolynomial_one N cN hcN delta hco hn P hP hr base Θ hnorm hp j)

/-- The same polynomial splitting preserves both specified preceding
ideals, keeping their two compatibility statements distinct. -/
theorem retainedPolynomial_two_ideals (hp : Odd p) (j : J)
    (I O : Ideal (N.obj (singletonIndex j)))
    (hI : ∀ a ∈ I, matchingPriorOperator N cN hcN delta hco hn base Θ j a ∈ I)
    (hO : ∀ a ∈ O, matchingPriorOperator N cN hcN delta hco hn base Θ j a ∈ O) :
    (retainedPolynomialSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp j).IsCompatible
      (I.map Polynomial.C) ∧
    (retainedPolynomialSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp j).IsCompatible
      (O.map Polynomial.C) :=
  ⟨retainedPolynomial_prior N cN hcN delta hco hn P hP hr base Θ hnorm hp j I hI,
    retainedPolynomial_prior N cN hcN delta hco hn P hP hr base Θ hnorm hp j O hO⟩
end Normalization
end SchubertGeometry.RetainedCharacter
