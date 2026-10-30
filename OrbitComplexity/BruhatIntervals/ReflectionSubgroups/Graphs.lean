import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Canonical
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Cosets

/-!
# Bruhat graphs of canonical subgroup systems

A Coxeter system on a subgroup whose simple generators are ambient canonical reflections has
the ambient reflection inversions and the induced ambient directed Bruhat graph. The proof uses
the inversion cocycle and induction by simple generators.

## Main results

* `canonical_inversion_iff`: intrinsic inversions equal ambient subgroup inversions.
* `canonical_bruhatStep_iff`: intrinsic edges equal the induced ambient Bruhat edges.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Theorem 1.4.
-/

namespace BruhatIntervals

variable {Index J W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {submatrix : CoxeterMatrix J} (cs : CoxeterSystem matrix W) (H : Subgroup W)
  (subsystem : CoxeterSystem submatrix H)

private theorem simple_inversion {G : Type*} [Group G] {M : CoxeterMatrix J}
    (system : CoxeterSystem M G) (i : J) (t : G) :
    system.IsLeftInversion (system.simple i) t ↔ t = system.simple i := by
  constructor
  · intro h
    have hzero : system.length (t * system.simple i) = 0 := by
      have := h.2
      rw [system.length_simple] at this
      omega
    have heq := system.length_eq_zero_iff.mp hzero
    have hback := congrArg (· * system.simple i) heq
    simpa only [system.simple_mul_simple_cancel_right, one_mul] using hback
  · rintro rfl
    exact ⟨system.isReflection_simple i, by simp only [system.simple_mul_simple_self,
      system.length_one, system.length_simple, Nat.zero_lt_succ]⟩

private theorem ambient_simple
    (hcanonical : ∀ i, (subsystem.simple i).val ∈ canonicalReflections cs H) (i : J) (t : H) :
    cs.IsLeftInversion (subsystem.simple i).val t.val ↔ t = subsystem.simple i := by
  constructor
  · intro hinv
    have hmem : t.val ∈
        {r | cs.IsLeftInversion (subsystem.simple i).val r ∧ r ∈ H} := ⟨hinv, t.property⟩
    rw [(hcanonical i).2, Set.mem_singleton_iff] at hmem
    exact Subtype.ext hmem
  · rintro rfl
    have hmem : (subsystem.simple i).val ∈
        {r | cs.IsLeftInversion (subsystem.simple i).val r ∧ r ∈ H} := by
      rw [(hcanonical i).2]
      exact Set.mem_singleton _
    exact hmem.1

/-- A subgroup Coxeter system with ambient canonical simple generators has exactly the ambient
restricted reflection inversions. -/
theorem canonical_inversion_iff
    (hcanonical : ∀ i, (subsystem.simple i).val ∈ canonicalReflections cs H) (h t : H) :
    subsystem.IsLeftInversion h t ↔ cs.IsLeftInversion h.val t.val := by
  suffices aux : ∀ h t : H,
      subsystem.IsLeftInversion h t ↔ cs.IsLeftInversion h.val t.val from aux h t
  intro h
  apply subsystem.simple_induction_left h
  · intro t
    simp only [CoxeterSystem.IsLeftInversion, subsystem.length_one, Subgroup.coe_one,
      cs.length_one, Nat.not_lt_zero, and_false]
  · intro h i ih t
    change subsystem.IsLeftInversion (subsystem.simple i * h) t ↔
      cs.IsLeftInversion ((subsystem.simple i).val * h.val) t.val
    rw [leftInversion_mul_iff, leftInversion_mul_iff,
      simple_inversion, ambient_simple cs H subsystem hcanonical, ih]
    rfl

/-- A subgroup Coxeter system with ambient canonical simple generators has the ambient induced
directed Bruhat graph. -/
theorem canonical_bruhatStep_iff
    (hcanonical : ∀ i, (subsystem.simple i).val ∈ canonicalReflections cs H) (h k : H) :
    subsystem.BruhatStep h k ↔ cs.BruhatStep h.val k.val := by
  rw [bruhatStep_iff_leftInversion, bruhatStep_iff_leftInversion]
  exact canonical_inversion_iff cs H subsystem hcanonical k (k * h⁻¹)

end BruhatIntervals
