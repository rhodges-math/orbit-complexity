import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierMap
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeTransitions
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPolynomialCoordinates
import OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Cartier construction from the preceding normalized word

The preceding global map constructs the node operators. Section values on the
same next-word matching line give their transition agreement and the raw local
Cartier maps. The original node geometry then glues those maps once.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private line chart from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private nodePrior from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
open private affinePolynomialMap projectiveRefinement projectiveRefinement_open from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private quadratic_degree from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private chartInsertedData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierSections
open private insertedLocal from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.NormalizedChartGluing
open private polynomial_chart_covers from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem chartInsertedData_of_operator_eq {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {A X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (k : A ⟶ X) [IsOpenImmersion k]
    (H : (frobeniusRestriction C p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange)
    (m : unitModule X ⟶ L) (Φ Ψ : SchemeFrobeniusMap Y p)
    (j : A ⟶ Y) [IsOpenImmersion j]
    (hcoord : chartInsertedData base L k H m Φ j) (hΦ : Ψ = Φ) :
    chartInsertedData base L k H m Ψ j := by
  subst Ψ
  exact hcoord

private def nodePolynomial {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) (n : ℕ)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val}) (s : {s : Finset J // s.Nonempty})
        :
    Polynomial (N.obj s) :=
  (Polynomial.map (N.map (singletonArrow s (sel s).1 (sel s).2)).hom.toRingHom
    (P (sel s).1)) ^ n

private def polynomialLeg {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R) {X : Scheme.{u}}
    (K : ∀ s, line (N.obj s) ⟶ X)
    (s : {s : Finset J // s.Nonempty}) (j : ULift.{u} (Fin 2)) :
    Spec (.of (Polynomial (N.obj s))) ⟶ X := chart (N.obj s) j ≫ K s

private instance polynomialLeg_open {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R) {X : Scheme.{u}}
    (K : ∀ s, line (N.obj s) ⟶ X) [∀ s, IsOpenImmersion (K s)]
    (s : {s : Finset J // s.Nonempty}) (j : ULift.{u} (Fin 2)) :
    IsOpenImmersion (polynomialLeg N K s j) := by
  dsimp only [polynomialLeg]
  infer_instance

private def polynomialCover {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R) {X : Scheme.{u}}
    (K : ∀ s, line (N.obj s) ⟶ X) [∀ s, IsOpenImmersion (K s)]
    (hcover : ∀ x : X, ∃ s y, K s y = x) : X.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers ({s : Finset J // s.Nonempty} × ULift.{u} (Fin 2))
    (fun i => Spec (.of (Polynomial (N.obj i.1))))
    (fun i => polynomialLeg N K i.1 i.2)
    (fun x => by
      obtain ⟨s, y, hy⟩ := hcover x
      obtain ⟨j, z, hz⟩ := polynomial_chart_covers (N.obj s) y
      exact ⟨(s, j), z, (congrArg (K s) hz).trans hy⟩)
    (fun i => by dsimp only [polynomialLeg]; infer_instance)

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

private def chartRaw (s : {s : Finset J // s.Nonempty}) (j : ULift.{u} (Fin 2)) :
    (frobeniusRestriction K p baseX L).over (polynomialLeg N Knode s j).opensRange ⟶
      (unitModule X).over (polynomialLeg N Knode s j).opensRange := by
  let : IsOpenImmersion (polynomialLeg N Knode s j) := by
    dsimp only [polynomialLeg]
    infer_instance
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  exact ProjectiveCartier.relativeCartierWordChart
    (nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2)
    j baseX L (polynomialLeg N Knode s j) (E s j)

private theorem chartRaw_insert (hp : Odd p)
    (s : {s : Finset J // s.Nonempty}) (j : ULift.{u} (Fin 2))
    (hs : sectionValue (polynomialLeg N Knode s j) L m (E s j).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (N.obj s)))).inv
        (sectionChartPolynomial (p - 1) (nodePolynomial N P ((p - 1) / 2) sel s) j.down))) :
    let : IsOpenImmersion (polynomialLeg N Knode s j) := by
      dsimp only [polynomialLeg]
      infer_instance
    let : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    let W := nodePolynomial N P ((p - 1) / 2) sel s
    let hW : W.natDegree ≤ p - 1 := quadratic_degree (P (sel s).1) (hP (sel s).1) _ p hp
    let mY := ProjectiveLine.projectivePolynomialSection (N.obj s) (p - 1) W hW
    chartInsertedData baseX L (polynomialLeg N Knode s j)
      (chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E s j) m
      (ProjectiveCartier.relativeCartierOperator (K := K)
        (nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2)
        (insertedInfinity mY)) (chart (N.obj s) j) := by
  let : IsOpenImmersion (polynomialLeg N Knode s j) := by
    dsimp only [polynomialLeg]
    infer_instance
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let W := nodePolynomial N P ((p - 1) / 2) sel s
  have hW : W.natDegree ≤ p - 1 := quadratic_degree (P (sel s).1) (hP (sel s).1) _ p hp
  exact ProjectiveCartier.relativePolynomialChart_section
    (nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2) j baseX L
    (polynomialLeg N Knode s j) (E s j)
    (chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E s j) rfl m W hW hs

private theorem chartRaw_coordinate (hp : Odd p)
    (s : {s : Finset J // s.Nonempty}) (j : ULift.{u} (Fin 2))
    (hs : sectionValue (polynomialLeg N Knode s j) L m (E s j).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (N.obj s)))).inv
        (sectionChartPolynomial (p - 1) (nodePolynomial N P ((p - 1) / 2) sel s) j.down))) :
    chartInsertedData baseX L (polynomialLeg N Knode s j)
      (chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E s j) m
      (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
        (sel s).1 (sel s).2).toOperator (chart (N.obj s) j) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  have hcoord := chartRaw_insert N cN hcN delta hco hn P hP base Θ sel
    Knode baseX L m E hp s j hs
  have hnode := retainedNodeSplitting_operator N cN hcN delta hco hn P hP hr base Θ hnorm
    hp s (sel s).1 (sel s).2
  let W := nodePolynomial N P ((p - 1) / 2) sel s
  have hW : W.natDegree ≤ p - 1 := quadratic_degree (P (sel s).1) (hP (sel s).1) _ p hp
  let mY := ProjectiveLine.projectivePolynomialSection (N.obj s) (p - 1) W hW
  let Φ : SchemeFrobeniusMap (line (N.obj s)) p :=
    ProjectiveCartier.relativeCartierOperator (K := K)
      (nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2) (insertedInfinity mY)
  let Ψ : SchemeFrobeniusMap (line (N.obj s)) p :=
    (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
      (sel s).1 (sel s).2).toOperator
  have leaf := chartInsertedData_of_operator_eq (A := Spec (.of (Polynomial (N.obj s))))
    (Y := line (N.obj s)) baseX L (polynomialLeg N Knode s j)
    (chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E s j) m
  exact leaf Φ Ψ (chart (N.obj s) j) hcoord hnode

/-- The preceding normalized word map and the next word's section/coframe
coordinates construct its normalized global Cartier map. Node operators, their
transition agreement, raw chart maps, their normalization, and the gluing are all
constructed from these data on the same global line. -/
theorem exists_retained_word_cartier (hp : Odd p) (hp' : 1 < p)
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
    ∃ ΘX : frobeniusRestriction K p baseX L ⟶ unitModule X,
      (∀ s j, ΘX.over (polynomialLeg N Knode s j).opensRange =
        chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E s j) ∧
      (∀ s j, (ProjectiveCartier.twistedSectionOperator baseX L ΘX
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).openPullback
          (polynomialLeg N Knode s j) =
        (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
          (sel s).1 (sel s).2).toOperator.openPullback (chart (N.obj s) j)) ∧
      (ProjectiveCartier.twistedSectionOperator baseX L ΘX ((m.val.app (op ⊤)).hom (1 : Γ(X,
          ⊤)))).onOpen ⊤ 1 = 1 := by
  let U := polynomialCover N Knode hcover
  let g : ∀ {s t : {s : Finset J // s.Nonempty}}, (s ⟶ t) → (line (N.obj t) ⟶ line (N.obj s)) :=
    fun {_ _} f => projectiveRefinement (N.map f).hom.toRingHom (a f) (b f)
  let : ∀ {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t), IsOpenImmersion (g f) :=
    fun {_ _} f => projectiveRefinement_open (N.map f).hom.toRingHom (a f) (b f)
  let φ := fun s =>
    (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
      (sel s).1 (sel s).2).toOperator
  have hφ : ∀ {s t} (f : s ⟶ t), (φ s).openPullback (g f) = φ t := by
    intro s t f
    have hs₀ := hsections s (⟨0⟩ : ULift.{u} (Fin 2))
    have ht₀ := hsections t (⟨0⟩ : ULift.{u} (Fin 2))
    have hs : sectionValue (polynomialLeg N Knode s ⟨0⟩) L m (E s ⟨0⟩).hom
        ((Scheme.ΓSpecIso (.of (Polynomial (N.obj s)))).inv
          (nodePolynomial N P ((p - 1) / 2) sel s)) := by
      simpa only [sectionChartPolynomial, ite_true] using hs₀
    have ht : sectionValue (polynomialLeg N Knode t ⟨0⟩) L m (E t ⟨0⟩).hom
        ((Scheme.ΓSpecIso (.of (Polynomial (N.obj t)))).inv
          (nodePolynomial N P ((p - 1) / 2) sel t)) := by
      simpa only [sectionChartPolynomial, ite_true] using ht₀
    exact retainedNodeSplitting_refine N cN hcN delta hco hn P hP hr base Θ hnorm hp hp'
      f (sel s).1 (sel s).2 (sel t).1 (sel t).2 (a f) (b f)
      X L m _ _ (htriangle f) (E s ⟨0⟩) (E t ⟨0⟩) hs ht
  have hφone : ∀ s, (φ s).onOpen ⊤ 1 = 1 := by
    intro s
    exact (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
      (sel s).1 (sel s).2).onOpen ⊤ |>.map_one
  let F : ∀ i : U.I₀, L.over (U.f i).opensRange ≅ (unitModule X).over (U.f i).opensRange :=
    fun i => OperatorSheaf.coframeOverRange (polynomialLeg N Knode i.1 i.2) L (E i.1 i.2)
  let k := fun i : U.I₀ => chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E i.1 i.2
  have hcoordinates : ∀ i : U.I₀,
      (OperatorSheaf.openOperatorEquiv K p baseX (U.f i).opensRange
        (insertedLocal baseX L m (U.f i).opensRange (k i))).openPullback
          (U.f i).isoOpensRange.hom = (φ i.1).openPullback (chart (N.obj i.1) i.2) := by
    intro i
    exact chartRaw_coordinate N cN hcN delta hco hn P hP hr base Θ hnorm sel
      Knode baseX L m E hp i.1 i.2 (hsections i.1 i.2)
  let aChart : ∀ i : U.I₀, U.X i ⟶ line (N.obj i.1) :=
    fun i => chart (N.obj i.1) i.2
  have factory := ProjectiveCartier.exists_word_cartier_map
    (Nat.lt_trans Nat.zero_lt_one hp') D cD hcD q (fun s => line (N.obj s)) rnode Knode
    hcart g htransition φ hφ hφone baseX L m U (fun i => i.1)
  obtain ⟨ΘX, hΘX, hInserted, hnormX⟩ := @factory aChart
    (fun i => projectiveLinePolynomialChart_open (N.obj i.1) i.2)
    (fun _ => rfl) F k hcoordinates
  exact ⟨ΘX, (fun s j => hΘX (s, j)), (fun s j => hInserted (s, j)), hnormX⟩

end SchubertGeometry.RetainedCharacter
