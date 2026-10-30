import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodePolynomials
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Word polynomials in the original append frames

The full singleton coefficient comparison and the original affine chart
projections determine the append-frame polynomial on every intersection.
All coefficients come from the same retained word polynomial family.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open ReductiveGroups GroupActions

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private selectedIndex selectedFrame selectedChart_singleton from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private wordPolynomialData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
open private framePolynomial framePullback from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections

private theorem polynomial_arrow_eq {A B : Type u} [CommRing A] [CommRing B]
    (a b : Spec (.of A) ⟶ Spec (.of B)) (h : a = b) (P : Polynomial B) :
    Polynomial.map (Spec.preimage a).hom P =
      Polynomial.map (Spec.preimage b).hom P :=
  congrArg (fun f => Polynomial.map (Spec.preimage f).hom P) h

/-- The full polynomial of a retained singleton word chart pulls back to the
original append-frame polynomial for every intersection and every chosen
endpoint chart, using the same affine projections. -/
theorem wordFramePolynomial_chart {K R J : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] [CommRing R]
    (G : ReductiveGroupData K) (i : G.rootBase.support)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (PN : ∀ s, Polynomial (N.obj s))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (hdata : wordPolynomialData G F point a i N v PN)
    (V : J → Over (Spec (.of K)))
    (b : ∀ j, V j ⟶ (oppositeUnipotentVariety G).toOver)
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V j)
    (hsingle : ∀ j, a j = p (singletonIndex j) j (Finset.mem_singleton_self j) ≫ b j)
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj)) :
    ∀ s j hj, Polynomial.map (v.app s).hom
      (Polynomial.map (N.map (singletonArrow s j hj)).hom.toRingHom
        (PN (singletonIndex j))) =
      framePolynomial G i (F.obj s) (p s j hj ≫ b j) (point j) := by
  have hQ (j : J) : Polynomial.map (v.app (singletonIndex j)).hom
      (PN (singletonIndex j)) =
      Polynomial.map (Spec.preimage (a j ≫ flagChartMap G (point j)).left).hom
        (DeterminantSection.simpleFramePolynomial G i
          (DeterminantSection.positiveDetCoefficient G)) := by
    exact ((hdata (singletonIndex j)).2.1).trans
      (polynomial_arrow_eq _ _
        (congrArg Over.Hom.left (selectedChart_singleton G F point a j)) _)
  have ha (j : J) : (a j ≫ flagChartMap G (point j)).left =
      (p (singletonIndex j) j (Finset.mem_singleton_self j)).left ≫
        (b j ≫ flagChartMap G (point j)).left := by
    exact (congrArg (fun f => (f ≫ flagChartMap G (point j)).left) (hsingle j)).trans
      (Category.assoc _ _ _)
  have hp (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
      Spec.map (CommRingCat.ofHom (F.map (singletonArrow s j hj)).hom.toRingHom) ≫
        (p (singletonIndex j) j (Finset.mem_singleton_self j)).left =
          (p s j hj).left :=
    congrArg Over.Hom.left
      (hpn (singletonIndex j) s (singletonArrow s j hj) j (Finset.mem_singleton_self j))
  have h := wordPolynomial_chart N F v (fun j => PN (singletonIndex j))
    (DeterminantSection.simpleFramePolynomial G i (DeterminantSection.positiveDetCoefficient G))
    (fun j => (V j).left)
    (fun j => (p (singletonIndex j) j (Finset.mem_singleton_self j)).left)
    (fun j => (b j ≫ flagChartMap G (point j)).left)
    (fun j => (a j ≫ flagChartMap G (point j)).left) ha
    (fun s j hj => (p s j hj).left) hp hQ
  intro s j hj
  change Polynomial.map (v.app s).hom
    (Polynomial.map (N.map (singletonArrow s j hj)).hom.toRingHom
      (PN (singletonIndex j))) =
    Polynomial.map (Spec.preimage ((p s j hj ≫ b j) ≫ flagChartMap G (point j)).left).hom
      (DeterminantSection.simpleFramePolynomial G i (DeterminantSection.positiveDetCoefficient G))
  exact (h s j hj).trans (polynomial_arrow_eq _ _ (Category.assoc _ _ _).symm _)

end SchubertGeometry.RetainedCharacter
