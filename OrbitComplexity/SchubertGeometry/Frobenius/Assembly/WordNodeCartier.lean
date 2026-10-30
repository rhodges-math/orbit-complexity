import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeBoundary
import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorCoverExt
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # A global word splitting and its projective nodes

Normalization of the global matching-line functional gives a splitting.
Its polynomial-chart formulas identify its restriction to each projective
node with the normalized splitting on that node.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.RetainedCharacter

open private unitModule polynomialLeg nodePolynomial from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private line chart from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private polynomial_chart_covers from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover
open private affinePolynomialMap projectiveRefinement from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates

private theorem normalizedOperator_eq {X : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (h : φ.onOpen ⊤ 1 = 1) :
    (φ.toSplitting 1 h).toOperator = φ := by
  apply SchemeFrobeniusMap.ext
  intro U a
  change (φ.toSplitting 1 h).onOpen U a = φ.onOpen U a
  rw [SchemeFrobeniusMap.toSplitting_apply, map_one, one_mul]

private theorem operator_on_node {A : Type u} [CommRing A]
    {X : Scheme.{u}} {p : ℕ} (k : line A ⟶ X) [IsOpenImmersion k]
    (φ : SchemeFrobeniusMap X p) (ψ : SchemeFrobeniusMap (line A) p)
    (h : ∀ j : ULift.{u} (Fin 2),
      φ.openPullback (chart A j ≫ k) = ψ.openPullback (chart A j)) :
    φ.openPullback k = ψ := by
  let U : (line A).OpenCover.{u} := Scheme.Cover.mkOfCovers
    (ULift.{u} (Fin 2)) (fun _ => Spec (.of (Polynomial A))) (chart A)
    (polynomial_chart_covers A) (fun j => projectiveLinePolynomialChart_open A j)
  apply SchemeFrobeniusMap.eq_of_openCover U
  intro j
  have : IsOpenImmersion (chart A j) := projectiveLinePolynomialChart_open A j
  exact (SchemeFrobeniusMap.openPullback_comp φ (chart A j) k).symm.trans (h j)

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
      unitModule cN.pt.left)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    {X : Scheme.{u}} (Knode : ∀ s, line (N.obj s) ⟶ X)
    [∀ s, IsOpenImmersion (Knode s)]
    (baseX : X ⟶ Spec (.of K)) (L : X.Modules) (m : unitModule X ⟶ L)
    (E : ∀ s j, (Scheme.Modules.pullback (polynomialLeg N Knode s j)).obj L ≅
      unitModule (Spec (.of (Polynomial (N.obj s)))))

/-- The normalized global word functional yields a splitting whose restriction
to every projective node is its prescribed normalized node operator. -/
theorem exists_word_node_splitting (hp : Odd p) (hp' : 1 < p)
    (D : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion (D.map f)]
    [(D ⋙ Scheme.forget).IsLocallyDirected]
    (cD : Cocone D) (hcD : IsColimit cD) (q : X ⟶ cD.pt)
    (rnode : ∀ s, line (N.obj s) ⟶ D.obj (op s))
    (hcart : ∀ s, IsPullback (rnode s) (Knode s) (cD.ι.app (op s)) q)
    (hcover : ∀ x : X, ∃ s y, Knode s y = x)
    (a : ∀ {s t : {s : Finset J // s.Nonempty}}, (s ⟶ t) → (N.obj t)ˣ)
    (b : ∀ {s t : {s : Finset J // s.Nonempty}}, (s ⟶ t) → N.obj t)
    (htransition : ∀ {s t} (f : s ⟶ t),
      projectiveRefinement (N.map f).hom.toRingHom (a f) (b f) ≫ Knode s = Knode t)
    (htriangle : ∀ {s t} (f : s ⟶ t),
      polynomialLeg N Knode t ⟨0⟩ = Spec.map (CommRingCat.ofHom
        (affinePolynomialMap (N.map f).hom.toRingHom (a f) (b f))) ≫
          polynomialLeg N Knode s ⟨0⟩)
    (hsections : ∀ s j, sectionValue (polynomialLeg N Knode s j) L m (E s j).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (N.obj s)))).inv
        (sectionChartPolynomial (p - 1) (nodePolynomial N P ((p - 1) / 2) sel s) j.down))) :
    ∃ (ΘX : frobeniusRestriction K p baseX L ⟶ unitModule X)
      (S : SchemeSplitting X p),
      S.toOperator = ProjectiveCartier.twistedSectionOperator baseX L ΘX
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) ∧
      ∀ s, S.toOperator.openPullback (Knode s) =
        (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
          (sel s).1 (sel s).2).toOperator := by
  obtain ⟨ΘX, _, hcharts, hnormal⟩ :=
    exists_retained_word_cartier N cN hcN delta hco hn P hP hr base Θ hnorm sel
      Knode baseX L m E hp hp' D cD hcD q rnode hcart hcover a b
      htransition htriangle hsections
  let φ : SchemeFrobeniusMap X p := ProjectiveCartier.twistedSectionOperator baseX L ΘX
    ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
  let S : SchemeSplitting X p := φ.toSplitting 1 hnormal
  have hS : S.toOperator = φ := normalizedOperator_eq φ hnormal
  refine ⟨ΘX, S, hS, ?_⟩
  intro s
  calc
    S.toOperator.openPullback (Knode s) = φ.openPullback (Knode s) :=
      congrArg (fun ψ : SchemeFrobeniusMap X p => ψ.openPullback (Knode s)) hS
    _ = _ := operator_on_node (Knode s) φ
      (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
        (sel s).1 (sel s).2).toOperator (hcharts s)

end SchubertGeometry.RetainedCharacter
