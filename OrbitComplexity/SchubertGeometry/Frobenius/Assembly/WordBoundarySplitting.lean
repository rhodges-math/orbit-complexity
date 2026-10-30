import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeCartier
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
import OrbitComplexity.FrobeniusSplitting.Compatible.CoverKernels
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The last omitted-letter boundary

The global word operator agrees with the normalized operator on every original
projective node. The local infinity ideals then give compatibility with the
kernel of the global section representing the last omitted letter.
-/

set_option autoImplicit false
noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private unitModule polynomialLeg nodePolynomial from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private affinePolynomialMap projectiveRefinement from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private matching_leg_open from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel

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



/-- Whole-node agreement transfers the local infinity ideals to the kernel of
the global omitted-letter section. -/
theorem retainedWord_infinity (hp : Odd p)
    (S : SchemeSplitting X p) (πX : X ⟶ cN.pt.left)
    (d : cN.pt.left ⟶ X) [IsClosedImmersion d]
    (hd : d ≫ πX = 𝟙 _)
    (hπ : ∀ s, projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
      (cN.ι.app (op s)).left = Knode s ≫ πX)
    (hsection : ∀ s, projectiveLineSection (N.obj s) (⟨1⟩ : ULift.{u} (Fin 2)) ≫
      Knode s = (cN.ι.app (op s)).left ≫ d)
    (hcover : ∀ x : X, ∃ s y, Knode s y = x)
    (hoperator : ∀ s, S.toOperator.openPullback (Knode s) =
      (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
        (sel s).1 (sel s).2).toOperator) :
    S.IsCompatible d.ker := by
  exact @SchemeSplitting.isCompatible_section_of_cover X cN.pt.left p S πX d
    inferInstance hd (expChar_pos K p) {s : Finset J // s.Nonempty}
    (fun s => Spec (.of (N.obj s))) (fun s => line (N.obj s))
    (fun s => (cN.ι.app (op s)).left) (fun s => matching_leg_open N cN hcN s)
    Knode inferInstance
    (fun s => projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)))
    (fun s => projectiveLineSection (N.obj s) (⟨1⟩ : ULift.{u} (Fin 2)))
    hπ hsection hcover
    (fun s => retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s
      (sel s).1 (sel s).2)
    hoperator
    (fun s => retainedNode_infinity N cN hcN delta hco hn P hP hr base Θ hnorm hp s
      (sel s).1 (sel s).2)

end SchubertGeometry.RetainedCharacter
