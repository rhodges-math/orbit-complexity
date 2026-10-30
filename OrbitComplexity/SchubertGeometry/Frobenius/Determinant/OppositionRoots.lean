import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRoots
import Batteries.Tactic.Lint

/-!
# The opposition permutation of simple roots

Negating the longest Weyl action preserves the positive roots and permutes
the simple roots. This identifies the simple coordinate obtained by
longest-Weyl conjugation of a root product.
-/

open ReductiveGroups

namespace SchubertGeometry.DeterminantSection

noncomputable section

section RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic]

private theorem height_one_support (b : P.Base) {i : ι}
    (hi : b.IsPos i) (hh : b.height i = 1) : i ∈ b.support := by
  have h : b.IsPos i ∧ (b.height i = 1 → i ∈ b.support) := by
    apply hi.induction_on_add
    · intro j hj
      exact ⟨b.isPos_of_mem_support hj, fun _ => hj⟩
    · intro j k l he hj hk
      refine ⟨hj.1.add (b.isPos_of_mem_support hk) he, ?_⟩
      intro hl
      have hadd := b.height_add he
      have hkheight : b.height k = 1 := RootPairing.Base.height_one_of_mem_support hk
      have hjpos : 0 < b.height j := hj.1
      omega
  exact h.2 hh

private theorem height_monotone (b : P.Base) (f : ι → ι)
    (hpos : ∀ i, b.IsPos i → b.IsPos (f i))
    (hadd : ∀ i j k, P.root k = P.root i + P.root j →
      P.root (f k) = P.root (f i) + P.root (f j)) {i : ι} (hi : b.IsPos i) :
    b.height i ≤ b.height (f i) := by
  have h : b.IsPos i ∧ b.height i ≤ b.height (f i) := by
    apply hi.induction_on_add
    · intro j hj
      have hjpos := b.isPos_of_mem_support hj
      refine ⟨hjpos, ?_⟩
      have hfj : 0 < b.height (f j) := hpos j hjpos
      have hjheight : b.height j = 1 := RootPairing.Base.height_one_of_mem_support hj
      omega
    · intro j k l he hj hk
      refine ⟨hj.1.add (b.isPos_of_mem_support hk) he, ?_⟩
      have hsum := b.height_add he
      have hfsum := b.height_add (hadd j k l he)
      have hfk : 0 < b.height (f k) := hpos k (b.isPos_of_mem_support hk)
      have hkheight : b.height k = 1 := RootPairing.Base.height_one_of_mem_support hk
      omega
  exact h.2

private theorem positive_involution_simple (b : P.Base) (f : ι → ι)
    (hpos : ∀ i, b.IsPos i → b.IsPos (f i))
    (hadd : ∀ i j k, P.root k = P.root i + P.root j →
      P.root (f k) = P.root (f i) + P.root (f j))
    (hinv : Function.Involutive f) (i : b.support) : f i ∈ b.support := by
  have hfi : b.IsPos (f i) := hpos i (b.isPos_of_mem_support i.property)
  have hlo : 0 < b.height (f i) := hfi
  have hhi := height_monotone b f hpos hadd hfi
  rw [hinv i] at hhi
  have hiheight : b.height i = 1 := RootPairing.Base.height_one_of_mem_support i.property
  exact height_one_support b hfi (by omega)

variable [P.IsReduced]

private def oppositionIndex (b : P.Base) (i : ι) : ι :=
  P.reflectionPerm (P.weylGroupToPerm (longestWeylElement b) i)
    (P.weylGroupToPerm (longestWeylElement b) i)

private theorem opposition_root (b : P.Base) (i : ι) :
    P.root (oppositionIndex b i) = - (longestWeylElement b • P.root i) := by
  unfold oppositionIndex
  rw [P.root_reflectionPerm, P.reflection_apply_self, ← P.weylGroup_apply_root]

private theorem opposition_positive (b : P.Base) (i : ι) (hi : b.IsPos i) :
    b.IsPos (oppositionIndex b i) :=
  (RootPairing.Base.IsPos.neg_iff_not b
    (P.weylGroupToPerm (longestWeylElement b) i)).mpr
      (longestWeylElement_not_isPos b hi)

private theorem opposition_add (b : P.Base) (i j k : ι)
    (h : P.root k = P.root i + P.root j) :
    P.root (oppositionIndex b k) =
      P.root (oppositionIndex b i) + P.root (oppositionIndex b j) := by
  rw [opposition_root, opposition_root, opposition_root, h, smul_add, neg_add]

private theorem opposition_involutive (b : P.Base) :
    Function.Involutive (oppositionIndex b) := by
  intro i
  apply P.root.injective
  rw [opposition_root, opposition_root, smul_neg, neg_neg, ← mul_smul,
    longestWeylElement_sq, one_smul]

private theorem opposition_support (b : P.Base) (i : b.support) :
    oppositionIndex b i ∈ b.support :=
  positive_involution_simple b (oppositionIndex b)
    (opposition_positive b) (opposition_add b) (opposition_involutive b) i

end RootPairing

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

/-- The simple root opposite to the longest-Weyl translate of a simple root. -/
def oppositionSimple (i : G.rootBase.support) : G.rootBase.support :=
  ⟨oppositionIndex G.rootBase i, opposition_support G.rootBase i⟩

/-- The opposition simple root is the negative of the longest-Weyl translate. -/
theorem oppositionSimple_root (i : G.rootBase.support) :
    G.rootSystem.root (oppositionSimple G i) =
      - (G.longestElement • G.rootSystem.root i) :=
  opposition_root G.rootBase i

/-- Applying opposition twice returns the original simple root. -/
theorem oppositionSimple_twice (i : G.rootBase.support) :
    oppositionSimple G (oppositionSimple G i) = i :=
  Subtype.ext (opposition_involutive G.rootBase i)

end

end SchubertGeometry.DeterminantSection
