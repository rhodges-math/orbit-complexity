import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionRepresentatives
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootParameters
import Batteries.Tactic.Lint

/-!
# The additive parameter in an opposition boundary chart

Conjugating the selected simple-root parameter by the inverse simple
representative and then the longest representative yields the opposition
simple-root parameter up to a sign. Its square is therefore unchanged.
-/

open ReductiveGroups

namespace SchubertGeometry.DeterminantSection

noncomputable section

private theorem signs_mul {R : Type*} [Ring R] {a b : R}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

private theorem conjugate_parameter {M R : Type*} [Group M] [Semigroup R]
    (w r : M) (x y z : R → M) (a b : R)
    (hr : ∀ t, r * x t * r⁻¹ = y (a * t))
    (hw : ∀ t, w * y t * w⁻¹ = z (b * t)) (t : R) :
    (w * r) * x t * (w * r)⁻¹ = z ((b * a) * t) := by
  calc
    (w * r) * x t * (w * r)⁻¹ = w * (r * x t * r⁻¹) * w⁻¹ := by group
    _ = w * y (a * t) * w⁻¹ := congrArg (fun q => w * q * w⁻¹) (hr t)
    _ = z (b * (a * t)) := hw (a * t)
    _ = z ((b * a) * t) := congrArg z (mul_assoc b a t).symm

private theorem negative_index_from_root {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (w : P.weylGroup) (i j n : ι)
    (hn : P.root n = - P.root (P.weylGroupToPerm w i))
    (hj : P.root j = - (w • P.root i)) : n = j := by
  apply P.root.injective
  exact hn.trans ((congrArg Neg.neg (P.weylGroup_apply_root w i)).symm.trans hj.symm)

private theorem reflection_self_index {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (i n : ι) (hn : P.root n = - P.root i) :
    P.reflectionPerm i i = n := by
  apply P.root.injective
  exact (P.root_reflectionPerm i i).trans ((P.reflection_apply_self i).trans hn.symm)

private theorem singleton_word_perm {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (b : P.Base) (i : b.support) :
    P.weylGroupToPerm (simpleWeylWord b [i]) i.val = P.reflectionPerm i.val i.val := by
  simp only [simpleWeylWord, mul_one, weylGroupToPerm_simple]

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

/-- The group point conjugating a positive simple coordinate to the opposition coordinate. -/
def oppositionConjugator (i : G.rootBase.support) : G.points :=
  G.longestPoint * (G.reflectionPoint i.val)⁻¹

/-- The specified root parameter in the translated opposition chart changes by a sign. -/
theorem oppositionSimple_parameter (i : G.rootBase.support) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
      oppositionConjugator G i * gaParameterPoint (G.simpleRootMap i) t *
          (oppositionConjugator G i)⁻¹ =
        gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t) := by
  obtain ⟨_, _, φ, _, _, hsimple, _, hweyl, hinverse⟩ := G.exists_pairedRootParameters
  obtain ⟨a, ha, hfirst⟩ := hinverse [i] i.val
  obtain ⟨b, hb, hsecond⟩ := hweyl G.longestElement i.val
  have hword : simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
      G.rootBase [i] = (G.reflectionPoint i.val)⁻¹ := by
    simp only [simpleWordPoint_cons, simpleWordPoint_nil, mul_one]
  have hindex : G.rootSystem.weylGroupToPerm (simpleWeylWord G.rootBase [i]) i.val =
      -i.val :=
    (singleton_word_perm G.rootSystem G.rootBase i).trans
      (reflection_self_index G.rootSystem i.val (-i.val) rfl)
  have hopposition : -(G.rootSystem.weylGroupToPerm G.longestElement i.val) =
      (oppositionSimple G i).val :=
    negative_index_from_root G.rootSystem G.longestElement i.val
      (oppositionSimple G i).val (-(G.rootSystem.weylGroupToPerm G.longestElement i.val))
      rfl (oppositionSimple_root G i)
  have hfirst' (t : K) :
      (G.reflectionPoint i.val)⁻¹ * gaParameterPoint (G.simpleRootMap i) t *
          ((G.reflectionPoint i.val)⁻¹)⁻¹ = gaParameterPoint (φ (-i.val)) (a * t) := by
    have h := (hfirst t).1
    simpa only [hword, hindex, (hsimple i).1] using h
  have hsecond' (t : K) :
      G.longestPoint * gaParameterPoint (φ (-i.val)) t * G.longestPoint⁻¹ =
        gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (b * t) := by
    have h := (hsecond t).2
    simpa only [ReductiveGroups.ReductiveGroupData.longestPoint, hopposition,
      (hsimple (oppositionSimple G i)).1] using h
  refine ⟨b * a, signs_mul hb ha, ?_⟩
  intro t
  exact conjugate_parameter G.longestPoint (G.reflectionPoint i.val)⁻¹
    (fun q => gaParameterPoint (G.simpleRootMap i) q)
    (fun q => gaParameterPoint (φ (-i.val)) q)
    (fun q => gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) q)
    a b hfirst' hsecond' t

end

end SchubertGeometry.DeterminantSection
