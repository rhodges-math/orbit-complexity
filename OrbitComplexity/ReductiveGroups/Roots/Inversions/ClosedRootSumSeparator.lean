import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootReflectionClosure
import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootRegularPerturbation
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

/-!
# Closed Root Sum Separator

The sum of a closed asymmetric root subset supplies a rational
strictly positive functional. -/

noncomputable section
namespace ReductiveGroups

private theorem sum_pos_of_reflection_pairs
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (σ : ι ≃ ι) (w : ι → ℚ)
    (hinv : ∀ j, σ (σ j) = j)
    (hflip : ∀ j, w (σ j) = -w j)
    (hclosed : ∀ j ∈ s, w j < 0 → σ j ∈ s)
    (i : ι) (hi : i ∈ s) (hw : 0 < w i) (hopp : σ i ∉ s) :
    0 < ∑ j ∈ s, w j := by
  let t := s.filter (fun j => w j < 0)
  let u := t.image σ
  have ht_sub : t ⊆ s := Finset.filter_subset _ _
  have hu_sub : u ⊆ s := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact hclosed k (ht_sub hk) (Finset.mem_filter.mp hk).2
  have htu : Disjoint t u := by
    apply Finset.disjoint_left.mpr
    intro j hjt hju
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hju
    have hjneg : w j < 0 := (Finset.mem_filter.mp hjt).2
    have hkneg : w k < 0 := (Finset.mem_filter.mp hk).2
    rw [← heq, hflip] at hjneg
    linarith
  have hu_sum : (∑ j ∈ u, w j) = -(∑ j ∈ t, w j) := by
    rw [Finset.sum_image]
    · simp_rw [hflip]
      rw [Finset.sum_neg_distrib]
    · exact σ.injective.injOn
  have hpair_sum : (∑ j ∈ t ∪ u, w j) = 0 := by
    rw [Finset.sum_union htu, hu_sum]
    exact add_neg_cancel _
  let r := s \ (t ∪ u)
  have hsum_r : (∑ j ∈ s, w j) = ∑ j ∈ r, w j := by
    have hsub : t ∪ u ⊆ s := Finset.union_subset ht_sub hu_sub
    have h := Finset.sum_sdiff hsub (f := w)
    rw [hpair_sum] at h
    simpa [r] using h.symm
  have hr_nonneg : ∀ j ∈ r, 0 ≤ w j := by
    intro j hj
    by_contra hn
    have hjt : j ∈ t := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, lt_of_not_ge hn⟩
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left u hjt)
  have hir : i ∈ r := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hi, ?_⟩
    intro hip
    rcases Finset.mem_union.mp hip with hit | hiu
    · exact (not_lt_of_ge hw.le) (Finset.mem_filter.mp hit).2
    · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hiu
      have : k = σ i := by rw [← heq, hinv]
      exact hopp (this ▸ ht_sub hk)
  rw [hsum_r]
  exact Finset.sum_pos' hr_nonneg ⟨i, hir, hw⟩

open RootPairing

universe u v w₁ w₂
variable {ι : Type u} {R : Type v} {M : Type w₁} {N : Type w₂}
  [Finite ι] [AddCommGroup M] [AddCommGroup N]
  [Field R] [CharZero R] [Module R M] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]

/-- The total Cartan pairing of a closed asymmetric root subset with each of
its own roots is strictly positive. -/
theorem closed_asymmetric_sum_pairing_pos
    (s : Set ι)
    (hopp : ∀ i ∈ s, ∀ j ∈ s, P.root i ≠ -P.root j)
    (hclosed : ∀ i ∈ s, ∀ j ∈ s, ∀ k, P.root k = P.root i + P.root j → k ∈ s)
    (i : ι) (hi : i ∈ s) :
    0 < ∑ j ∈ (Set.toFinite s).toFinset, (P.pairingIn ℤ j i : ℚ) := by
  classical
  let S : Finset ι := (Set.toFinite s).toFinset
  let σ : ι ≃ ι := P.reflectionPerm i
  let w : ι → ℚ := fun j => (P.pairingIn ℤ j i : ℚ)
  have hinv (j : ι) : σ (σ j) = j := P.reflectionPerm_self i j
  have hflip (j : ι) : w (σ j) = -w j := by
    change (P.pairingIn ℤ (P.reflectionPerm i j) i : ℚ) =
      -(P.pairingIn ℤ j i : ℚ)
    exact_mod_cast ((P.pairingIn_reflectionPerm ℤ i j i).symm.trans
      (P.pairingIn_reflectionPerm_self_right ℤ j i))
  have hs (j : ι) (hj : j ∈ S) (hjneg : w j < 0) : σ j ∈ S := by
    have hjneg' : P.pairingIn ℤ j i < 0 := by
      change (P.pairingIn ℤ j i : ℚ) < 0 at hjneg
      exact_mod_cast hjneg
    simpa [S, σ] using ClosedRootReflectionClosure.root_reflection_mem_of_pairing_neg P s hopp
      hclosed hi
      (by simpa [S] using hj) hjneg'
  have hwi : 0 < w i := by simp [w]
  have hoppi : σ i ∉ S := by
    intro hσ
    have hroot : P.root (σ i) = -P.root i := by
      simp [σ, P.root_reflectionPerm]
    have hcontra := hopp i hi (σ i) (by simpa [S] using hσ)
    simp [hroot] at hcontra
  exact sum_pos_of_reflection_pairs S σ w hinv hflip hs i
    (by simpa [S] using hi) hwi hoppi

omit [Finite ι] [P.IsReduced] in
private theorem posRootForm_two_mul_eq_pairing
    [Fintype ι] [Module ℚ M] [IsScalarTower ℚ R M]
    (j i : ι) :
    2 * (P.posRootForm ℚ).posForm (P.rootSpanMem ℚ j) (P.rootSpanMem ℚ i) =
      P.pairingIn ℚ j i *
        (P.posRootForm ℚ).posForm (P.rootSpanMem ℚ i) (P.rootSpanMem ℚ i) := by
  apply FaithfulSMul.algebraMap_injective ℚ R
  simp only [map_mul, map_ofNat, P.algebraMap_posRootForm_posForm,
    P.algebraMap_pairingIn]
  exact (P.posRootForm ℚ).two_mul_apply_root_root j i

/-- A closed asymmetric root subset admits one rational form strictly positive
on every member. The form is obtained from the sum of its roots. -/
theorem ClosedRootSumSeparator.exists_form_of_closed_asymmetric
    (s : Set ι)
    (hopp : ∀ i ∈ s, ∀ j ∈ s, P.root i ≠ -P.root j)
    (hclosed : ∀ i ∈ s, ∀ j ∈ s, ∀ k, P.root k = P.root i + P.root j → k ∈ s) :
    ∃ f : M →+ ℚ, ∀ i ∈ s, 0 < f (P.root i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let S : Finset ι := (Set.toFinite s).toFinset
  let B := (P.posRootForm ℚ).posForm
  let ρ : P.rootSpan ℚ := ∑ j ∈ S, P.rootSpanMem ℚ j
  let fW : P.rootSpan ℚ →ₗ[ℚ] ℚ := B ρ
  obtain ⟨fM, hfM⟩ := LinearMap.exists_extend fW
  refine ⟨fM.toAddMonoidHom, ?_⟩
  intro i hi
  let ri := P.rootSpanMem ℚ i
  have hlen : 0 < B ri ri := (P.posRootForm ℚ).rootLength_pos i
  have hsumPos : 0 < ∑ j ∈ S, P.pairingIn ℚ j i := by
    simpa only [S, P.pairingIn_rat] using
      closed_asymmetric_sum_pairing_pos P s hopp hclosed i hi
  have heval : fM (P.root i) = B ρ ri := by
    have h := LinearMap.congr_fun hfM ri
    simpa [fW, ri] using h
  have hsumB : B ρ ri = ∑ j ∈ S, B (P.rootSpanMem ℚ j) ri := by
    simp [ρ, map_sum]
  have hmul : 2 * B ρ ri = (∑ j ∈ S, P.pairingIn ℚ j i) * B ri ri := by
    rw [hsumB, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    exact posRootForm_two_mul_eq_pairing P j i
  have hprod : 0 < (∑ j ∈ S, P.pairingIn ℚ j i) * B ri ri :=
    mul_pos hsumPos hlen
  have hB : 0 < B ρ ri := by nlinarith [hmul]
  rw [← heval] at hB
  exact hB

/-- A closed asymmetric subset of a finite reduced crystallographic root
system lies in the positive cone of a compatible base. -/
theorem exists_base_containing_closed_asymmetric
    [P.IsRootSystem]
    (s : Set ι)
    (hopp : ∀ i ∈ s, ∀ j ∈ s, P.root i ≠ -P.root j)
    (hclosed : ∀ i ∈ s, ∀ j ∈ s, ∀ k, P.root k = P.root i + P.root j → k ∈ s) :
    ∃ b : P.Base, ∀ i ∈ s,
      P.root i ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)) := by
  obtain ⟨f, hf⟩ := ClosedRootSumSeparator.exists_form_of_closed_asymmetric P s hopp hclosed
  obtain ⟨g, hreg, hpos⟩ := exists_regular_positive_root_form P s f hf
  exact ClosedRootFunctionalBase.exists_roots_of_regular_positive_form P s g hreg hpos

end ReductiveGroups
