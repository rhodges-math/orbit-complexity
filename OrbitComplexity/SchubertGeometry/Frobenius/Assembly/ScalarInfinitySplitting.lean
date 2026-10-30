import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundarySplitting
import OrbitComplexity.SchubertGeometry.Normality.Bundles.InfinityDiagram
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Infinity compatibility on a prescribed scalar word model

The arithmetic infinity section has a closed scalar section on the same
prescribed fibre as the word operator. Its node maps are the original
projective infinity sections, as determined by the two Cartesian projections.
The normalized node operators therefore preserve its global kernel.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private unitModule from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private infinity_coeff infinity_base from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.InfinityDiagram
open private projective_pullback from
  OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange

private theorem node_base_equation {C : Type*} [Category C]
    {P A B X T : C} (p : P ⟶ A) (a : A ⟶ B) (b : B ⟶ T)
    (c : A ⟶ T) (k : P ⟶ X) (baseX : X ⟶ T)
    (ha : a ≫ b = c) (hk : k ≫ baseX = p ≫ c) :
    k ≫ baseX = p ≫ a ≫ b := by
  exact hk.trans (congrArg (fun f => p ≫ f) ha.symm)

variable {K J : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of K))) (hcN : IsColimit cN)
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
    (Θ : frobeniusRestriction K p cN.pt.hom
      (matchingModule N cN delta ((p - 1) / 2)) ⟶ unitModule cN.pt.left)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})

end SchubertGeometry.RetainedCharacter
