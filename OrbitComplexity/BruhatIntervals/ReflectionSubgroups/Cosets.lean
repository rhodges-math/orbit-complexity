import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Cocycle
import OrbitComplexity.BruhatIntervals.Order.Basic

/-!
# Bruhat graphs on subgroup cosets

A minimum-length representative of a right coset has no left inversions in its subgroup.
The inversion cocycle then shows that right translation by this representative preserves the
directed Bruhat edges between subgroup elements.

## Main results

* `exists_minimal_coset`: a right coset has a minimum-length representative without subgroup
  inversions.
* `leftInversion_mul_of_coset`: translation preserves subgroup reflection inversions.
* `bruhatStep_iff_leftInversion`: an upward edge is an inversion at its upper endpoint.
* `bruhatStep_mul_coset_iff`: translation preserves directed Bruhat edges in the subgroup.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Theorem 1.4.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- Every right coset has a minimum-length representative without subgroup left inversions. -/
theorem exists_minimal_coset (H : Subgroup W) (x : W) :
    ∃ z : W, z * x⁻¹ ∈ H ∧
      (∀ h ∈ H, cs.length z ≤ cs.length (h * x)) ∧
      ∀ t ∈ H, ¬cs.IsLeftInversion z t := by
  classical
  have hex : ∃ n : ℕ, ∃ h ∈ H, cs.length (h * x) = n :=
    ⟨cs.length x, 1, H.one_mem, by rw [one_mul]⟩
  obtain ⟨h, hh, hlength⟩ := Nat.find_spec hex
  refine ⟨h * x, by simpa only [mul_inv_cancel_right] using hh, ?_, ?_⟩
  · intro k hk
    rw [hlength]
    exact Nat.find_min' hex ⟨k, hk, rfl⟩
  · intro t ht hinv
    have hmin := Nat.find_min' hex ⟨t * h, H.mul_mem ht hh, rfl⟩
    have hlt := hinv.2
    rw [mul_assoc] at hmin
    omega

/-- Translation by a coset representative with no subgroup inversions preserves all subgroup
reflection inversion memberships. -/
theorem leftInversion_mul_of_coset (H : Subgroup W) (z : W)
    (hz : ∀ t ∈ H, ¬cs.IsLeftInversion z t) {h t : W} (hh : h ∈ H) (ht : t ∈ H) :
    cs.IsLeftInversion (h * z) t ↔ cs.IsLeftInversion h t := by
  have hnot : ¬cs.IsLeftInversion z (h⁻¹ * t * h) :=
    hz _ (H.mul_mem (H.mul_mem (H.inv_mem hh) ht) hh)
  rw [leftInversion_mul_iff]
  simp only [Xor, hnot, not_false_eq_true, and_true, false_and, or_false]

/-- A directed Bruhat edge is exactly the associated reflection inversion at its upper endpoint. -/
theorem bruhatStep_iff_leftInversion (h k : W) :
    cs.BruhatStep h k ↔ cs.IsLeftInversion k (k * h⁻¹) := by
  constructor
  · rintro ⟨t, ht, rfl, hlt⟩
    simp only [mul_inv_cancel_right]
    refine ⟨ht, ?_⟩
    simpa only [← mul_assoc, ht.mul_self, one_mul] using hlt
  · intro hinv
    have hback : (k * h⁻¹) * k = h := by
      calc
        (k * h⁻¹) * k = (k * h⁻¹)⁻¹ * k := by rw [hinv.1.inv]
        _ = h := by group
    exact ⟨k * h⁻¹, hinv.1, by group, by simpa only [hback] using hinv.2⟩

/-- Translation by a coset representative with no subgroup inversions preserves the directed
Bruhat graph induced on the subgroup. -/
theorem bruhatStep_mul_coset_iff (H : Subgroup W) (z : W)
    (hz : ∀ t ∈ H, ¬cs.IsLeftInversion z t) {h k : W} (hh : h ∈ H) (hk : k ∈ H) :
    cs.BruhatStep (h * z) (k * z) ↔ cs.BruhatStep h k := by
  rw [bruhatStep_iff_leftInversion, bruhatStep_iff_leftInversion]
  have heq : k * z * (h * z)⁻¹ = k * h⁻¹ := by group
  rw [heq]
  exact leftInversion_mul_of_coset cs H z hz hk (H.mul_mem hk (H.inv_mem hh))

end BruhatIntervals
