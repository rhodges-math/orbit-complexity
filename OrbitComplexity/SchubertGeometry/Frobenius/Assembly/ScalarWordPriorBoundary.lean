import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordRawBoundary
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Raw preservation of earlier boundaries on a scalar word fibre

Cartesian polynomial charts transport earlier boundary ideals to the same
Cartier morphism and splitting on the scalar fibre. Preservation holds on
all open subsets.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

open private unitModule chartRaw polynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private nodePrior from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
open private chartRaw_ideal wordChartCoefficient_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierIdeals
open private polynomial_cartesian boundaryChart boundaryChart_cartesian projection_triangle from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorBoundary
open private raw_inserted_compatible from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordRawBoundary
open private polynomial_chart_covers from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover

namespace SchubertGeometry.RetainedCharacter

private theorem pullback_left_cast {D : Type*} [Category D]
    {P A B T : D} {j : P ⟶ A} {b : P ⟶ B} {q q' : A ⟶ T} {d : B ⟶ T}
    (hq : q = q') (h : IsPullback j b q d) : IsPullback j b q' d := by
  cases hq
  exact h

private theorem ideal_preserves_eq {A : Type*} [CommRing A] {p : ℕ}
    (φ : FrobeniusLinearMap A p) (I J : Ideal A) (h : I = J)
    (hI : ∀ a ∈ I, φ a ∈ I) : ∀ a ∈ J, φ a ∈ J := by
  cases h
  exact hI

variable {C R J : Type u} [Field C] [CommRing R] [Algebra C R]
    {p : ℕ} [ExpChar C p] [PerfectRing C p]
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
    (basePrior : cN.pt.left ⟶ Spec (.of C))
    (Θ : frobeniusRestriction C p basePrior
      (matchingModule N cN delta ((p - 1) / 2)) ⟶ unitModule cN.pt.left)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})

/-- The chosen scalar word Cartier morphism preserves a pulled-back earlier
boundary on every open. Its section-inserted splitting preserves the same
boundary ideal. The prior coefficient condition is transported through the
Cartesian affine charts. -/
theorem scalarWord_raw_prior {X Y Z : Scheme.{u}}
    (baseX : X ⟶ Spec (.of C)) (L : X.Modules) (m : unitModule X ⟶ L)
    (ΘX : frobeniusRestriction C p baseX L ⟶ unitModule X)
    (S : SchemeSplitting X p)
    (hS : S.toOperator = ProjectiveCartier.twistedSectionOperator baseX L ΘX
      (m.app ⊤ (1 : Γ(X, ⊤))))
    (Knode : ∀ s, line (N.obj s) ⟶ X) [∀ s, IsOpenImmersion (Knode s)]
    (E : ∀ s j, (Scheme.Modules.pullback (polynomialLeg N Knode s j)).obj L ≅
      unitModule (Spec (.of (Polynomial (N.obj s)))))
    (hraw : ∀ s j, ΘX.over (polynomialLeg N Knode s j).opensRange =
      chartRaw N cN hcN delta hco hn basePrior Θ sel Knode baseX L E s j)
    (q : X ⟶ cN.pt.left) (d : Y ⟶ cN.pt.left)
    (f : Z ⟶ X) [QuasiCompact f] (z : Z ⟶ Y) (hcart : IsPullback f z q d)
    (B : {s : Finset J // s.Nonempty} → Type u) [∀ s, CommRing (B s)]
    (g : ∀ s, N.obj s →+* B s) (b : ∀ s, Spec (.of (B s)) ⟶ Y)
    (hprior : ∀ s, IsPullback (Spec.map (CommRingCat.ofHom (g s))) (b s)
      (cN.ι.app (op s)).left d)
    (hπ : ∀ s, projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
      (cN.ι.app (op s)).left = Knode s ≫ q)
    (hcover : ∀ x : X, ∃ s y, Knode s y = x)
    (hI : ∀ s, ∀ a ∈ RingHom.ker (g s),
      nodePrior N cN hcN delta hco hn basePrior Θ s (sel s).1 (sel s).2 a ∈
        RingHom.ker (g s)) :
    S.IsCompatible f.ker ∧
      ∀ (V : X.Opens) (a : Γ(X, V)), f.app V a = 0 →
        ∀ e : Γ(L, V), f.app V (ΘX.app V (a • e)) = 0 := by
  classical
  let Idx := {s : Finset J // s.Nonempty} × ULift.{u} (Fin 2)
  let k : ∀ i : Idx, Spec (.of (Polynomial (N.obj i.1))) ⟶ X :=
    fun i => polynomialLeg N Knode i.1 i.2
  let a : ∀ i : Idx, Spec (.of (Polynomial (N.obj i.1))) ⟶ Spec (.of (N.obj i.1)) :=
    fun i => Spec.map (CommRingCat.ofHom (Polynomial.C : N.obj i.1 →+* Polynomial (N.obj i.1)))
  let j : ∀ i : Idx, Spec (.of (Polynomial (B i.1))) ⟶
      Spec (.of (Polynomial (N.obj i.1))) :=
    fun i => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (g i.1)))
  let c : ∀ i : Idx, Spec (.of (Polynomial (B i.1))) ⟶ Y := fun i =>
    Spec.map (CommRingCat.ofHom (Polynomial.C : B i.1 →+* Polynomial (B i.1))) ≫ b i.1
  have hk (i : Idx) : k i ≫ q = a i ≫ (cN.ι.app (op i.1)).left :=
    projection_triangle (projectiveLinePolynomialChart (N.obj i.1) i.2)
      (Knode i.1) (projectiveToSpec (N.obj i.1) (ULift.{u} (Fin 2)))
      (cN.ι.app (op i.1)).left q (a i)
      (projectiveLinePolynomialChart_base (N.obj i.1) i.2) (hπ i.1)
  have hpoly (i : Idx) : IsPullback (j i) (c i) (k i ≫ q) d :=
    pullback_left_cast (hk i).symm ((polynomial_cartesian (g i.1)).paste_vert (hprior i.1))
  have hw (i : Idx) : (j i ≫ k i) ≫ q = c i ≫ d :=
    (Category.assoc (j i) (k i) q).trans ((hpoly i).w)
  let bX : ∀ i : Idx, Spec (.of (Polynomial (B i.1))) ⟶ Z := fun i =>
    boundaryChart f z q d hcart (j i) (k i) (c i) (hw i)
  have hcartX (i : Idx) : IsPullback (j i) (bX i) (k i) f :=
    boundaryChart_cartesian f z q d hcart (j i) (k i) (c i) (hw i) (hpoly i)
  have hcoverX : ∀ x : X, ∃ i : Idx, ∃ y, k i y = x := by
    intro x
    obtain ⟨s, y, hy⟩ := hcover x
    obtain ⟨l, a, hl⟩ := polynomial_chart_covers (N.obj s) y
    exact ⟨(s, l), a, (congrArg (Knode s) hl).trans hy⟩
  have hcoeff (i : Idx) : ∀ a ∈ RingHom.ker (Polynomial.mapRingHom (g i.1)),
      ProjectiveCartier.wordChartCoefficient baseX L (k i) (E i.1 i.2)
        (ΘX.over (k i).opensRange) a ∈ RingHom.ker (Polynomial.mapRingHom (g i.1)) := by
    have hnext := wordChartCoefficient_eq baseX L (k i) (E i.1 i.2) _ _
      (hraw i.1 i.2) ((RingHom.ker (g i.1)).map Polynomial.C)
        (chartRaw_ideal N cN hcN delta hco hn basePrior Θ sel Knode baseX L E
          i.1 i.2 (RingHom.ker (g i.1)) (hI i.1))
    exact ideal_preserves_eq _ _ _ (Polynomial.ker_mapRingHom (g i.1)).symm hnext
  have hrawf := @ProjectiveCartier.raw_cartier_kernel_of_charts
    C _ p _ (expChar_pos C p) X Z baseX L ΘX f inferInstance Idx
    (fun i => Polynomial (N.obj i.1)) (fun i => Polynomial (B i.1))
    (fun i => inferInstance) (fun i => inferInstance) k
    (fun i => by dsimp only [k, polynomialLeg]; infer_instance)
    (fun i => Polynomial.mapRingHom (g i.1)) bX hcartX
    (fun i => E i.1 i.2) hcoverX hcoeff
  exact ⟨raw_inserted_compatible baseX L ΘX f m S hS hrawf, hrawf⟩

end SchubertGeometry.RetainedCharacter
