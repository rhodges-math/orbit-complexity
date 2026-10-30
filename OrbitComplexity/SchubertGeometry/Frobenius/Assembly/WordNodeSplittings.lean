import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeNormalization
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedSplitting
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalized operators on the retained projective nodes

Each original intersection ring receives its prior functional by restriction of
the preceding global matching-line map. The retained quadratic construction is
then applied on that same ring with its singleton coefficient map.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private quadratic_degree from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting

variable {K R J : Type u} [Field K] [CommRing R] [Algebra K R]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
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
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) * (delta s j hj k hk : N.obj s))
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta ((p - 1) / 2)) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

private abbrev nodePrior (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    FrobeniusLinearMap (N.obj s) p :=
  ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
    (matchingModule N cN delta ((p - 1) / 2)) Θ s
    (retainedMatchingFrameSection N cN hcN delta ((p - 1) / 2) hco hn s j hj 1)

omit [Algebra K R] [PerfectRing K p] in
include hr hnorm in
private theorem nodePrior_normalized (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    nodePrior N cN hcN delta hco hn base Θ s j hj
      (((N.map (singletonArrow s j hj)).hom ((P j).coeff 2)) ^ ((p - 1) / 2)) = 1 := by
  have h := retainedPrior_normalized_node N cN hcN delta ((p - 1) / 2) hco hn
    (fun j => (P j).coeff 2) hr base Θ hnorm s j hj 1
  simpa only [Units.val_one, mul_one] using h

/-- The preceding global matching-line map constructs the normalized
splitting on every retained projective node, without changing its coefficient ring. -/
def retainedNodeSplitting (hp : Odd p) (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) : SchemeSplitting (line (N.obj s)) p := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  exact ProjectiveCartier.retainedQuadraticSplitting (K := K) (P j) (hP j)
    (N.map (singletonArrow s j hj)).hom.toRingHom
    (nodePrior N cN hcN delta hco hn base Θ s j hj) hp
    (nodePrior_normalized N cN hcN delta hco hn P hr base Θ hnorm s j hj)

/-- The constructed node splitting uses the same Cartier operator and the
same retained polynomial section that enter the polynomial-chart comparison. -/
theorem retainedNodeSplitting_operator (hp : Odd p)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    let : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    let f := (N.map (singletonArrow s j hj)).hom.toRingHom
    let m := ProjectiveLine.projectivePolynomialSection (N.obj s) (p - 1)
      ((Polynomial.map f (P j)) ^ ((p - 1) / 2)) (quadratic_degree (P j) (hP j) f p hp)
    (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s j hj).toOperator =
      ProjectiveCartier.relativeCartierOperator (K := K)
        (nodePrior N cN hcN delta hco hn base Θ s j hj) (insertedInfinity m) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  exact ProjectiveCartier.retainedQuadratic_operator (K := K) (P j) (hP j)
    (N.map (singletonArrow s j hj)).hom.toRingHom
    (nodePrior N cN hcN delta hco hn base Θ s j hj) hp
    (nodePrior_normalized N cN hcN delta hco hn P hr base Θ hnorm s j hj)

end SchubertGeometry.RetainedCharacter
