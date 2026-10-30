import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorNormalization
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingTraceAgreement
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Prior normalization on every retained node

The global preceding-word section normalizes its singleton prior operators.
Restriction to an intersection and the adjusted matching-frame rule give the
normalization on every original retained coefficient ring.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private retainedCoordinateIso from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
open private retainedRange_le from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameRestriction

private theorem unit_idempotent {A : Type u} [CommMonoid A] (d : Aˣ) (h : d = d * d) :
    d = 1 :=
  mul_left_cancel (h.symm.trans (mul_one d).symm)

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (r : ∀ j, N.obj (singletonIndex j))
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (r j) =
        (N.map (singletonArrow s k hk)).hom (r k) * (delta s j hj k hk : N.obj s))

/-- The preceding normalized global matching map normalizes the adjusted prior
functional on every retained node, in that node's coefficient ring. -/
theorem retainedPrior_normalized_node {K : Type u} [CommRing K]
    {p : ℕ} [ExpChar K p] (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app (coefficientMatchingSection N cN delta r hr n) ⊤).hom
        (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) :
    ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
      (matchingModule N cN delta n) Θ s
      (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)
      (((N.map (singletonArrow s j hj)).hom (r j) * (d : N.obj s)) ^ n) = 1 := by
  let f : singletonIndex j ⟶ s := singletonArrow s j hj
  have hres := retainedMatchingFrame_restrict N cN hcN delta n hco hn f j
    (Finset.mem_singleton_self j) 1 1 (by simp only [map_one])
  have hchange := retainedMatchingFrame_change N cN hcN delta n hco hn s j hj j hj 1 d
  have he := hres.trans hchange
  have hmap := ProjectiveCartier.retainedTwistedPriorOperator_map N cN hcN base
    (matchingModule N cN delta n) Θ f
    (retainedMatchingFrameSection N cN hcN delta n hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j) 1)
    (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)
    (retainedMatchingFrameFactor N cN hcN delta n s j hj j hj 1 d)
    (retainedRange_le N cN hcN f) he ((r j) ^ n)
  have hsource₀ := retainedPrior_normalized N cN hcN delta n hco hn r hr base Θ hnorm j 1
  have hsource : ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
      (matchingModule N cN delta n) Θ (singletonIndex j)
      (retainedMatchingFrameSection N cN hcN delta n hco hn
        (singletonIndex j) j (Finset.mem_singleton_self j) 1) ((r j) ^ n) = 1 := by
    simpa only [Units.val_one, mul_one] using hsource₀
  have hδ : delta s j hj j hj = 1 := unit_idempotent _ (hco s j hj j hj j hj)
  have hfactor := ProjectiveCartier.retainedFrameFactor_coefficient
    N cN hcN delta n s j hj j hj 1 d
  have hfactor' : (retainedCoordinateIso N cN hcN s).hom
      (retainedMatchingFrameFactor N cN hcN delta n s j hj j hj 1 d) = (d : N.obj s) ^ n := by
    exact hfactor.trans (by simp only [hδ, one_mul, inv_pow, inv_inv, Units.val_pow_eq_pow_val])
  let ψ := ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
    (matchingModule N cN delta n) Θ s
    (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)
  have harg : (retainedCoordinateIso N cN hcN s).hom
      (retainedMatchingFrameFactor N cN hcN delta n s j hj j hj 1 d) * (N.map f).hom ((r j) ^ n) =
      ((N.map f).hom (r j) * (d : N.obj s)) ^ n := by
    rw [hfactor', map_pow, mul_pow]
    exact mul_comm _ _
  have hright : (N.map f).hom
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ (singletonIndex j)
        (retainedMatchingFrameSection N cN hcN delta n hco hn
          (singletonIndex j) j (Finset.mem_singleton_self j) 1) ((r j) ^ n)) = 1 :=
    (congrArg (N.map f).hom hsource).trans (N.map f).hom.map_one
  exact (congrArg ψ harg).symm.trans (hmap.trans hright)

end SchubertGeometry.RetainedCharacter
