import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierIdeals
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedSplitting
import OrbitComplexity.FrobeniusSplitting.Compatible.CoverKernels
import OrbitComplexity.FrobeniusSplitting.Compatible.Morphisms
import OrbitComplexity.FrobeniusSplitting.Compatible.ClosedQuotient
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.RingHom.Integral
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Earlier boundary ideals under a Cartier append

Polynomial base change identifies the earlier boundary on each append chart.
The same section-inserted Cartier map therefore preserves the global pullback
boundary kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
open FrobeniusSplitting.RetainedCharacter
open GroupActions

namespace SchubertGeometry.ProjectiveCartier

private theorem polynomial_cartesian {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
      (Spec.map (CommRingCat.ofHom f)) := by
  algebraize [f, Polynomial.mapRingHom f]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout A B (Polynomial A) (Polynomial B))).flip

private theorem polynomial_kernel_compatible {A B : Type u} [CommRing A] [CommRing B]
    {p : ℕ} (ρ : RingSplitting (Polynomial A) p) (f : A →+* B)
    (hf : Function.Surjective f) (hp : 0 < p)
    (hI : ρ.IsCompatible ((RingHom.ker f).map Polynomial.C)) :
    (ρ.toSpec hp).IsCompatible
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))).ker := by
  let g := Polynomial.mapRingHom f
  have hg : Function.Surjective g := Polynomial.map_surjective f hf
  have hker : ρ.IsCompatible (RingHom.ker g) := by
    rw [Polynomial.ker_mapRingHom]
    exact hI
  let σ := ρ.ofSurjective g hg hker
  exact SchemeSplitting.isCompatible_ker (σ.toSpec hp) (ρ.toSpec hp)
    (Spec.map (CommRingCat.ofHom g))
    (ρ.toSpec_naturality σ hp g (fun a => ρ.ofSurjective_map g hg hker a))

private def boundaryChart {A B X Y Z T : Scheme.{u}}
    (f : Z ⟶ X) (z : Z ⟶ Y) (q : X ⟶ T) (d : Y ⟶ T)
    (h : IsPullback f z q d) (j : B ⟶ A) (k : A ⟶ X) (b : B ⟶ Y)
    (w : (j ≫ k) ≫ q = b ≫ d) : B ⟶ Z :=
  h.lift (j ≫ k) b w

private theorem boundaryChart_cartesian {A B X Y Z T : Scheme.{u}}
    (f : Z ⟶ X) (z : Z ⟶ Y) (q : X ⟶ T) (d : Y ⟶ T)
    (h : IsPullback f z q d) (j : B ⟶ A) (k : A ⟶ X) (b : B ⟶ Y)
    (w : (j ≫ k) ≫ q = b ≫ d) (hchart : IsPullback j b (k ≫ q) d) :
    IsPullback j (boundaryChart f z q d h j k b w) k f := by
  let t := boundaryChart f z q d h j k b w
  have ht₁ : t ≫ f = j ≫ k := h.lift_fst _ _ w
  have ht₂ : t ≫ z = b := h.lift_snd _ _ w
  have houter : IsPullback j (t ≫ z) (k ≫ q) d := ht₂.symm ▸ hchart
  exact houter.of_bot ht₁.symm h

private theorem projection_triangle {A P B X Y : Scheme.{u}}
    (a : A ⟶ P) (k : P ⟶ X) (r : P ⟶ B) (b : B ⟶ Y) (q : X ⟶ Y)
    (c : A ⟶ B) (ha : a ≫ r = c) (hk : r ≫ b = k ≫ q) :
    (a ≫ k) ≫ q = c ≫ b := by
  rw [Category.assoc, ← hk, ← Category.assoc, ha]

private theorem pullback_operator_eq {A X : Scheme.{u}} {p : ℕ}
    (φ ψ : SchemeFrobeniusMap X p) (h : φ = ψ)
    (k : A ⟶ X) [IsOpenImmersion k] :
    φ.openPullback k = ψ.openPullback k :=
  congrArg (fun ξ : SchemeFrobeniusMap X p => ξ.openPullback k) h

end SchubertGeometry.ProjectiveCartier

namespace SchubertGeometry.RetainedCharacter

open ProjectiveLine

open private chart_openPullback from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedPullback

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private line chart from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private chartOpen from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private nodePrior nodePrior_normalized from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
open private polynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private polynomial_chart_covers from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

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

private theorem retainedNode_prior (hp : Odd p)
    (s : {s : Finset J // s.Nonempty}) (I : Ideal (N.obj s))
    (hI : ∀ a ∈ I, nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2 a ∈ I)
    (j : ULift.{u} (Fin 2)) :
    ∃ ρ : RingSplitting (Polynomial (N.obj s)) p,
      (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
        (sel s).1 (sel s).2).toOperator.openPullback (chart (N.obj s) j) =
          (ρ.toSpec (expChar_pos K p)).toOperator ∧
      ρ.IsCompatible (I.map Polynomial.C) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  obtain ⟨ρ, hρ, hρI⟩ := ProjectiveCartier.retainedQuadratic_prior (K := K)
    (P (sel s).1) (hP (sel s).1)
    (N.map (singletonArrow s (sel s).1 (sel s).2)).hom.toRingHom
    (nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2) hp
    (nodePrior_normalized N cN hcN delta hco hn P hr base Θ hnorm s (sel s).1 (sel s).2)
    I hI j
  refine ⟨ρ, ?_, hρI⟩
  exact chart_openPullback (chartOpen (N.obj s) j)
    (projectiveLinePolynomialIso (N.obj s) j)
    (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
      (sel s).1 (sel s).2).toOperator
    (ρ.toSpec (expChar_pos K p)).toOperator hρ.symm

end SchubertGeometry.RetainedCharacter
