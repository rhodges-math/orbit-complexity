import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorNormalization
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedSplitting
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalized quadratic charts from the retained word section

The preceding global functional supplies the normalization of the quadratic
leading coefficient through the retained matching section. The constructed
splitting preserves infinity and each extended ideal preserved by the prior
operator; its Cartier operator uses the determinant section itself.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter GroupActions
namespace SchubertGeometry.RetainedCharacter
universe u

open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private line indices
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private chartOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private insertedInfinity
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private quadratic_degree
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

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
      unitModule cN.pt.left)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr
          ((p - 1) / 2)) ⊤).hom (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

private abbrev matchingPriorOperator (j : J) :
    FrobeniusLinearMap (N.obj (singletonIndex j)) p :=
  ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
    (matchingModule N cN delta ((p - 1) / 2)) Θ (singletonIndex j)
    (retainedMatchingFrameSection N cN hcN delta ((p - 1) / 2) hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j) 1)

omit [Algebra K R] [PerfectRing K p] in
include hr hnorm in
private theorem matchingPrior_normalized (j : J) :
    matchingPriorOperator N cN hcN delta hco hn base Θ j
      ((P j).coeff 2 ^ ((p - 1) / 2)) = 1 := by
  have h := retainedPrior_normalized N cN hcN delta ((p - 1) / 2) hco hn
    (fun j => (P j).coeff 2) hr base Θ hnorm j 1
  simpa only [Units.val_one, mul_one] using h

/-- Coefficient algebras compose the base algebra with the chart algebra. -/
local instance coefficientAlgebra (s : {s : Finset J // s.Nonempty}) : Algebra K (N.obj s) :=
  ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra

/-- The retained quadratic append chart has a splitting whose normalization
comes from evaluation of the preceding global matching section. -/
def retainedMatchingSplitting (hp : Odd p) (j : J) :
    SchemeSplitting (line (N.obj (singletonIndex j))) p :=
  ProjectiveCartier.retainedQuadraticSplitting (K := K) (P j) (hP j)
    (RingHom.id (N.obj (singletonIndex j)))
    (matchingPriorOperator N cN hcN delta hco hn base Θ j) hp
    (matchingPrior_normalized N cN hcN delta hco hn P hr base Θ hnorm j)

/-- The normalized retained append splitting preserves the infinity section. -/
theorem retainedMatching_infinity (hp : Odd p) (j : J) :
    (retainedMatchingSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp j).IsCompatible
      (projectiveLineSection (N.obj (singletonIndex j)) (⟨1⟩ : indices.{u})).ker :=
  ProjectiveCartier.retainedQuadratic_infinity (K := K) (P j) (hP j)
    (RingHom.id (N.obj (singletonIndex j)))
    (matchingPriorOperator N cN hcN delta hco hn base Θ j) hp
    (matchingPrior_normalized N cN hcN delta hco hn P hr base Θ hnorm j)

/-- Each prior invariant ideal is preserved by the normalized polynomial
chart representative of the same retained append splitting. -/
theorem retainedMatching_prior (hp : Odd p) (j : J)
    (I : Ideal (N.obj (singletonIndex j)))
    (hI : ∀ a ∈ I, matchingPriorOperator N cN hcN delta hco hn base Θ j a ∈ I)
    (k : indices.{u}) :
    ∃ ρ : RingSplitting (Polynomial (N.obj (singletonIndex j))) p,
      (ρ.toOperator.toSpec (expChar_pos K p)).pushforward
          (projectiveLinePolynomialIso (N.obj (singletonIndex j)) k).hom =
        (retainedMatchingSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp
            j).toOperator.restrict
          (chartOpen (N.obj (singletonIndex j)) k) ∧
      ρ.IsCompatible (I.map Polynomial.C) :=
  ProjectiveCartier.retainedQuadratic_prior (K := K) (P j) (hP j)
    (RingHom.id (N.obj (singletonIndex j)))
    (matchingPriorOperator N cN hcN delta hco hn base Θ j) hp
    (matchingPrior_normalized N cN hcN delta hco hn P hr base Θ hnorm j) I hI k

/-- The retained append splitting is the Cartier operator with the retained
quadratic determinant section inserted. -/
theorem retainedMatching_operator (hp : Odd p) (j : J) :
    let A := N.obj (singletonIndex j)
    let m := ProjectiveLine.projectivePolynomialSection A (p - 1)
      ((Polynomial.map (RingHom.id A) (P j)) ^ ((p - 1) / 2))
      (quadratic_degree (P j) (hP j) (RingHom.id A) p hp)
    (retainedMatchingSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp j).toOperator =
      ProjectiveCartier.relativeCartierOperator (K := K)
        (matchingPriorOperator N cN hcN delta hco hn base Θ j) (insertedInfinity m) :=
  ProjectiveCartier.retainedQuadratic_operator (K := K) (P j) (hP j)
    (RingHom.id (N.obj (singletonIndex j)))
    (matchingPriorOperator N cN hcN delta hco hn base Θ j) hp
    (matchingPrior_normalized N cN hcN delta hco hn P hr base Θ hnorm j)

end SchubertGeometry.RetainedCharacter
