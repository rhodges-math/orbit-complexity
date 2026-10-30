import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoordinateIso
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameRestriction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Trace agreement with the complete matching factor

The coefficient of the inverse matching-frame transition is identified before
it is inserted into the affine Cartier comparison. All character powers and
both unit changes remain in that transition.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter Polynomial
namespace SchubertGeometry.RetainedCharacter
universe u

open private retainedChartRange retainedCoordinateIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

open private retainedRange_le
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameRestriction

private theorem trace_scalar {A : Type u} [CommRing A] {B : Type u}
    (τ : Polynomial A → B) (Q : Polynomial A) (a x y : A) (hxy : x = y)
    (r : B) (h : τ (C (x * a) * Q) = r) : τ (C (y * a) * Q) = r :=
  (congrArg (fun z : A => τ (C (z * a) * Q)) hxy).symm.trans h

variable {R J : Type u} [CommRing R]
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

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p] [Algebra K R]

/-- Refinement and a change of matching coframe give the affine trace
comparison with the entire transported inverse character-power coefficient. -/
theorem retainedMatchingTrace_refine
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t)
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ t.val)
    (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hp : 0 < p) (a : (N.obj t)ˣ) (b : N.obj t) (Q : Polynomial (N.obj s)) :
    letI : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    letI : Algebra K (N.obj t) :=
      ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
    let d' := Units.map (N.map f).hom.toMonoidHom d
    polynomialTraceOfOperator (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ t
        (retainedMatchingFrameSection N cN hcN delta n hco hn t k hk e))
      (C (((((delta t j ((leOfHom f) hj) k hk * d' * e⁻¹) ^ n)⁻¹ :
          (N.obj t)ˣ) : N.obj t) * (↑(a⁻¹) : N.obj t) ^ (p - 1)) *
        (Polynomial.map (N.map f).hom.toRingHom Q).comp
          (C (a : N.obj t) * X + C b)) =
    (Polynomial.map (N.map f).hom.toRingHom
      (polynomialTraceOfOperator (K := K)
        (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
          (matchingModule N cN delta n) Θ s
          (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)) Q)).comp
            (C (a : N.obj t) * X + C b) := by
  let d' := Units.map (N.map f).hom.toMonoidHom d
  have hres := retainedMatchingFrame_restrict N cN hcN delta n hco hn
    f j hj d d' rfl
  have hchange := retainedMatchingFrame_change N cN hcN delta n hco hn
    t j ((leOfHom f) hj) k hk d' e
  have he := hres.trans hchange
  have h := ProjectiveCartier.retainedAffinePriorTrace_map N cN hcN base
    (matchingModule N cN delta n) Θ f
    (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)
    (retainedMatchingFrameSection N cN hcN delta n hco hn t k hk e)
    (retainedMatchingFrameFactor N cN hcN delta n t j ((leOfHom f) hj) k hk d' e)
    (retainedRange_le N cN hcN f) he hp a b Q
  have hcoeff := ProjectiveCartier.retainedFrameFactor_coefficient
    N cN hcN delta n t j ((leOfHom f) hj) k hk d' e
  exact trace_scalar _ _ _ _ _ hcoeff _ h

/-- The affine trace comparison has the inverse of the entire adjusted
matching-unit power as its prior-line coefficient. -/
theorem retainedMatchingTrace_exact
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ)
    (hp : 0 < p) (a : (N.obj s)ˣ) (b : N.obj s) (Q : Polynomial (N.obj s)) :
    letI : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    polynomialTraceOfOperator (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ s
        (retainedMatchingFrameSection N cN hcN delta n hco hn s k hk e))
      (C (((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s) *
          (↑(a⁻¹) : N.obj s) ^ (p - 1)) *
        Q.comp (C (a : N.obj s) * X + C b)) =
    (polynomialTraceOfOperator (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ s
        (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)) Q).comp
          (C (a : N.obj s) * X + C b) := by
  have h := retainedMatchingFrameTrace N cN hcN delta n hco hn
    base Θ s j hj k hk d e hp a b Q
  have hcoeff := ProjectiveCartier.retainedFrameFactor_coefficient
    N cN hcN delta n s j hj k hk d e
  exact trace_scalar _ _ _ _ _ hcoeff _ h

end SchubertGeometry.RetainedCharacter
