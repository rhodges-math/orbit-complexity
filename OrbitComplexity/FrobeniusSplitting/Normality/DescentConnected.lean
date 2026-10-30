import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ContractionQuotient
import OrbitComplexity.FrobeniusSplitting.Normality.PolynomialConnected

/-!
# Connected spectra of descended polynomial contractions

The zero and one equations, and the scalar-valued origin, are derived from the
specified surjective coordinate map. Thus no connectedness assertion or origin on
the quotient is assumed. The remaining hypotheses concern only the original
polynomial family and its given Laurent kernel equation.

The original cell still needs to produce that Laurent equation and its scalar
origin identification; this generic application does not supply them.
-/

open AlgebraicGeometry

noncomputable section

namespace FrobeniusSplitting

universe u v w

/-- A descended polynomial contraction connects its specified nonempty quotient
spectrum, including nilpotents and nonclosed points. -/
theorem spec_connected_of_descent
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    {C : Type w} [CommRing C] [Nontrivial C] [Algebra K C]
    (q : A →ₐ[K] C) (hq : Function.Surjective q)
    (α : A →ₐ[K] Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q.toRingHom (α f)) = 0)
    (ε : A →ₐ[K] K)
    (hOne : ∀ a : A, (α a).eval 1 = a)
    (hZero : ∀ a : A, (α a).eval 0 = algebraMap K A (ε a)) :
    ConnectedSpace (Spec (.of C)) := by
  have hcoeff : Function.Injective (algebraMap K C) := (algebraMap K C).injective
  exact spec_connected_of_polynomial
    (polynomialDescent q hq α hLaurent)
    (polynomialOrigin q hq hcoeff α hLaurent ε hZero)
    (polynomialDescent_one q hq α hLaurent hOne)
    (polynomialDescent_zero q hq hcoeff α hLaurent ε hZero)

end FrobeniusSplitting
