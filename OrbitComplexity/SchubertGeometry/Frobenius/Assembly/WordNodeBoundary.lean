import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Boundary compatibility on the projective nodes

The normalized splitting on each intersection node preserves the ideal of
its infinity section. The normalization is the restriction of the same
preceding global matching-line functional.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private nodePrior nodePrior_normalized from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings

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


/-- The normalized splitting on each original intersection node preserves
the ideal of its infinity section. -/
theorem retainedNode_infinity (hp : Odd p)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s j hj).IsCompatible
      (projectiveLineSection (N.obj s) (⟨1⟩ : ULift.{u} (Fin 2))).ker := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  exact ProjectiveCartier.retainedQuadratic_infinity (K := K) (P j) (hP j)
    (N.map (singletonArrow s j hj)).hom.toRingHom
    (nodePrior N cN hcN delta hco hn base Θ s j hj) hp
    (nodePrior_normalized N cN hcN delta hco hn P hr base Θ hnorm s j hj)

end SchubertGeometry.RetainedCharacter
