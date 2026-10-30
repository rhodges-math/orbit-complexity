import OrbitComplexity.ReductiveGroups.Roots.Coxeter.LongestCount
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSubgroup
import TauCeti.GroupTheory.Coxeter.Bruhat
import Mathlib.Tactic

/-! # The longest element and Bruhat order

The longest element complements inversion length. Its multiplication reverses each
reflection step and hence reverses the strong Bruhat order on both sides.
-/

open CategoryTheory
namespace ReductiveGroups
noncomputable section
variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

private theorem longest_inv (b : P.Base) :
    (longestWeylElement b)⁻¹ = longestWeylElement b := by
  apply mul_left_cancel (a := longestWeylElement b)
  rw [mul_inv_cancel, longestWeylElement_sq]

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
private theorem count_eq_ncard (b : P.Base) (w : P.weylGroup) :
    rootInversionCount b w = (leftRootInversionIndices b w).ncard := by
  rw [rootInversionCount, leftRootInversions]
  exact Set.ncard_image_of_injective _ P.root.injective

private theorem longest_complement (b : P.Base) (w : P.weylGroup) :
    leftRootInversionIndices b (w⁻¹ * longestWeylElement b) =
      {i | b.IsPos i} \ leftRootInversionIndices b w⁻¹ := by
  ext i
  simp only [mem_leftRootInversionIndices, Set.mem_sdiff, Set.mem_ofPred_eq,
    mul_inv_rev, longest_inv, inv_inv, map_mul, Equiv.Perm.mul_apply,
    longestWeylElement_isPos_iff]
  tauto

/-- Multiplication on the left by the longest element complements inversion length. -/
theorem rootCount_longest_mul_add (b : P.Base) (w : P.weylGroup) :
    rootInversionCount b (longestWeylElement b * w) + rootInversionCount b w =
      rootInversionCount b (longestWeylElement b) := by
  have hsubset : leftRootInversionIndices b w⁻¹ ⊆ {i | b.IsPos i} := by
    intro i hi
    exact (mem_leftRootInversionIndices b w⁻¹ i).mp hi |>.1
  have hc := Set.ncard_sdiff_add_ncard_of_subset hsubset
  rw [← longest_complement b w, ← count_eq_ncard, ← count_eq_ncard] at hc
  have he : w⁻¹ * longestWeylElement b = (longestWeylElement b * w)⁻¹ := by
    rw [mul_inv_rev, longest_inv]
  simpa only [he, rootInversionCount_inv, ← rootInversionCount_longest] using hc


/-- Multiplication on the right by the longest element complements inversion length. -/
private theorem rootCount_mul_longest_add (b : P.Base) (w : P.weylGroup) :
    rootInversionCount b (w * longestWeylElement b) + rootInversionCount b w =
      rootInversionCount b (longestWeylElement b) := by
  have h := rootCount_longest_mul_add b w⁻¹
  have he := rootInversionCount_inv b (w * longestWeylElement b)
  rw [mul_inv_rev, longest_inv] at he
  simpa only [he, rootInversionCount_inv] using h

private theorem longest_step (b : P.Base) {u v : P.weylGroup}
    (h : (weylCoxeterSystem b).BruhatStep u v) :
    (weylCoxeterSystem b).BruhatStep (longestWeylElement b * v)
      (longestWeylElement b * u) := by
  obtain ⟨t, ht, rfl, hlt⟩ := h
  refine ⟨longestWeylElement b * t * (longestWeylElement b)⁻¹,
    ht.conj (longestWeylElement b), ?_, ?_⟩
  · symm
    calc
      _ = longestWeylElement b * (t * t) * u := by group
      _ = _ := by rw [ht.mul_self, mul_one]
  · have hu := rootCount_longest_mul_add b u
    have hv := rootCount_longest_mul_add b (t * u)
    simp only [← weylCoxeterSystem_length] at hu hv
    omega

private theorem longest_antitone (b : P.Base) {u v : P.weylGroup}
    (h : (weylCoxeterSystem b).BruhatLE u v) :
    (weylCoxeterSystem b).BruhatLE (longestWeylElement b * v)
      (longestWeylElement b * u) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl a => exact Relation.ReflTransGen.refl
  | single h => exact Relation.ReflTransGen.single (longest_step b h)
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- Left multiplication by the longest element reverses strong Bruhat order. -/
theorem bruhat_longest_mul_iff (b : P.Base) (u v : P.weylGroup) :
    (weylCoxeterSystem b).BruhatLE (longestWeylElement b * u)
      (longestWeylElement b * v) ↔ (weylCoxeterSystem b).BruhatLE v u := by
  constructor
  · intro h
    simpa only [← mul_assoc, longestWeylElement_sq, one_mul] using longest_antitone b h
  · exact longest_antitone b

/-- Right multiplication by the longest element reverses strong Bruhat order. -/
private theorem bruhat_mul_longest_iff (b : P.Base) (u v : P.weylGroup) :
    (weylCoxeterSystem b).BruhatLE (u * longestWeylElement b)
      (v * longestWeylElement b) ↔ (weylCoxeterSystem b).BruhatLE v u := by
  have h := (weylCoxeterSystem b).bruhatLE_inv_iff
    (u := u * longestWeylElement b) (w := v * longestWeylElement b)
  rw [mul_inv_rev, mul_inv_rev, longest_inv, bruhat_longest_mul_iff,
    (weylCoxeterSystem b).bruhatLE_inv_iff] at h
  exact h.symm

end
end ReductiveGroups
