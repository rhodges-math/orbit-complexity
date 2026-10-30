import OrbitComplexity.GroupActions.MomentMaps.FiniteHulls
import OrbitComplexity.GroupActions.MomentMaps.PositiveOrbit
import Batteries.Tactic.Lint

/-! # Relative interiors of exposed faces

Every point of a finite convex hull lies in the intrinsic interior of a nonempty exposed face.
Maximal positive supports of barycentric coefficients determine the exposing functional.
-/

open Set Filter
open scoped BigOperators Topology
noncomputable section
namespace GroupActions
universe u v

section Coefficients
variable {I : Type u} [Fintype I]

private theorem exists_positive_support (Q : Set (I → ℝ)) (hQ : Convex ℝ Q)
    (hne : Q.Nonempty) (hnonneg : ∀ a ∈ Q, ∀ i, 0 ≤ a i) :
    ∃ b ∈ Q, ∀ i, (∃ a ∈ Q, 0 < a i) → 0 < b i := by
  classical
  have build : ∀ s : Finset I, ∃ b ∈ Q, ∀ i ∈ s, (∃ a ∈ Q, 0 < a i) → 0 < b i := by
    intro s
    induction s using Finset.induction with
    | empty =>
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, hb, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨b, hb, hbpos⟩ := ih
      by_cases hex : ∃ a ∈ Q, 0 < a i
      · obtain ⟨a, ha, hai⟩ := hex
        refine ⟨(1 / 2 : ℝ) • b + (1 / 2 : ℝ) • a,
          hQ hb ha (by norm_num) (by norm_num) (by norm_num), ?_⟩
        intro j hj hpossible
        have hbj := hnonneg b hb j
        have haj := hnonneg a ha j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · nlinarith
        · have hbjpos := hbpos j hjs hpossible
          nlinarith
      · refine ⟨b, hb, ?_⟩
        intro j hj hpossible
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact (hex hpossible).elim
        · exact hbpos j hjs hpossible
  obtain ⟨b, hb, hpos⟩ := build Finset.univ
  exact ⟨b, hb, fun i => hpos i (Finset.mem_univ i)⟩


variable {E : Type v} [AddCommGroup E] [Module ℝ E]

private theorem positive_support_relation (w : I → E) (q : E) (b : I → ℝ)
    (hb : (∀ i, 0 ≤ b i) ∧ ∑ i, b i = 1 ∧ ∑ i, b i • w i = q)
    (hmax : ∀ i, (∃ c : I → ℝ, ((∀ j, 0 ≤ c j) ∧ ∑ j, c j = 1 ∧
      ∑ j, c j • w j = q) ∧ 0 < c i) → 0 < b i)
    (a : I → ℝ) (hzero : ∑ i, a i • ((1 : ℝ), w i) = 0)
    (ha : ∀ i, i ∉ Function.support b → 0 ≤ a i) :
    ∀ i, i ∉ Function.support b → a i = 0 := by
  have hmass : ∑ i, a i = 0 := by
    have h := congrArg Prod.fst hzero
    simpa only [Prod.fst_sum, Prod.smul_mk, smul_eq_mul, mul_one, Prod.fst_zero] using h
  have hweight : ∑ i, a i • w i = 0 := by
    have h := congrArg Prod.snd hzero
    simpa only [Prod.snd_sum, Prod.smul_mk, Prod.snd_zero] using h
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, b i ≠ 0 → 0 < b i + ε * a i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hbi : b i = 0
    · exact Filter.Eventually.of_forall (fun _ hi => (hi hbi).elim)
    have hbiPos : 0 < b i := lt_of_le_of_ne (hb.1 i) (Ne.symm hbi)
    have hcont : Continuous (fun ε : ℝ => b i + ε * a i) := by fun_prop
    have hlim : Tendsto (fun ε : ℝ => b i + ε * a i) (𝓝 0) (𝓝 (b i)) := by
      simpa only [zero_mul, add_zero] using hcont.tendsto 0
    exact (hlim.eventually (Ioi_mem_nhds hbiPos)).mono (fun _ h _ => h)
  have hepsilon : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hbound⟩ :=
    (hepsilon.and (hevent.filter_mono nhdsWithin_le_nhds)).exists
  let c : I → ℝ := fun i => b i + ε * a i
  have hc : (∀ i, 0 ≤ c i) ∧ ∑ i, c i = 1 ∧ ∑ i, c i • w i = q := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : b i = 0
      · have hai := ha i (by simpa only [Function.mem_support, not_ne_iff] using hi)
        simpa only [c, hi, zero_add] using mul_nonneg hε.le hai
      · exact (hbound i hi).le
    · simp only [c, Finset.sum_add_distrib, ← Finset.mul_sum, hb.2.1, hmass,
        mul_zero, add_zero]
    · simp only [c, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
        hb.2.2, hweight, smul_zero, add_zero]
  intro i hi
  by_contra hai
  have haiPos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hai)
  have hbi : b i = 0 := by simpa only [Function.mem_support, not_ne_iff] using hi
  have hcPos : 0 < c i := by simpa only [c, hbi, zero_add] using mul_pos hε haiPos
  exact (ne_of_gt (hmax i ⟨c, hc, hcPos⟩)) hbi



end Coefficients

/-- Every point of a finite convex hull lies in the intrinsic interior of an exposed face. -/
theorem exists_exposed_intrinsicInterior {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (w : I → E) (q : E)
    (hq : q ∈ convexHull ℝ (Set.range w)) :
    ∃ F : Set E, F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (Set.range w)) F ∧
      q ∈ intrinsicInterior ℝ F := by
  classical
  let Q : Set (I → ℝ) := {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧ ∑ i, a i • w i = q}
  have hQ : Convex ℝ Q := by
    intro a ha b hb r s hr hs hrs
    refine ⟨fun i => add_nonneg (mul_nonneg hr (ha.1 i)) (mul_nonneg hs (hb.1 i)), ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ha.2.1, hb.2.1, mul_one, hrs]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, ← Finset.smul_sum, ha.2.2, hb.2.2]
      rw [← add_smul, hrs, one_smul]
  have hne : Q.Nonempty := by
    have hq' : q ∈ convexHull ℝ (w '' (Set.univ : Set I)) := by
      simpa only [Set.image_univ] using hq
    obtain ⟨a, ha, _, hsum, hweight⟩ := (hull_image_coefficients w Set.univ q).mp hq'
    exact ⟨a, ha, hsum, hweight⟩
  obtain ⟨b, hb, hmax⟩ := exists_positive_support Q hQ hne (fun a ha => ha.1)
  have hbne : b ≠ 0 := by
    intro hzero
    have h := hb.2.1
    simp only [hzero, Pi.zero_apply, Finset.sum_const_zero] at h
    exact zero_ne_one h
  have hS : (Function.support b).Nonempty := Function.support_nonempty_iff.mpr hbne
  have hrel := positive_support_relation w q b hb hmax
  obtain ⟨f, hfzero, hfneg⟩ := exists_exposing_form
    (fun i => ((1 : ℝ), w i)) (Function.support b) hrel
  let ℓ : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inr ℝ ℝ E)
  have heval (i : I) : f ((1 : ℝ), w i) = f ((1 : ℝ), (0 : E)) + ℓ (w i) := by
    simpa only [ℓ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add] using f.map_add ((1 : ℝ), (0 : E)) (0, w i)
  have hvalue (i : I) (hi : i ∈ Function.support b) :
      ℓ (w i) = -f ((1 : ℝ), (0 : E)) := by
    have h := hfzero i hi
    rw [heval] at h
    linarith
  have hstrict (i : I) (hi : i ∉ Function.support b) :
      ℓ (w i) < -f ((1 : ℝ), (0 : E)) := by
    have h := hfneg i hi
    rw [heval] at h
    linarith
  have hbound (i : I) : ℓ (w i) ≤ -f ((1 : ℝ), (0 : E)) := by
    by_cases hi : i ∈ Function.support b
    · exact (hvalue i hi).le
    · exact (hstrict i hi).le
  let : Nonempty (Function.support b) := hS.to_subtype
  have hsumS : (∑ i, b i) = ∑ i : Function.support b, b i.val :=
    Finset.sum_congr_set (Function.support b) b (fun i => b i.val) (fun _ _ => rfl)
      (fun _ hi => by simpa only [Function.mem_support, not_ne_iff] using hi)
  have hweightS : (∑ i, b i • w i) = ∑ i : Function.support b, b i.val • w i.val := by
    apply Finset.sum_congr_set (Function.support b) _ _ (fun _ _ => rfl)
    intro i hi
    have hbi : b i = 0 := by simpa only [Function.mem_support, not_ne_iff] using hi
    rw [hbi, zero_smul]
  have hbar : Finset.univ.centerMass (fun i : Function.support b => b i.val)
      (fun i => w i.val) = q := by
    rw [Finset.centerMass, ← hsumS, hb.2.1, inv_one, one_smul, ← hweightS, hb.2.2]
  have hri := centerMass_mem_intrinsicInterior (fun i : Function.support b => w i.val)
    (fun i => b i.val) (fun i => lt_of_le_of_ne (hb.1 i.val) (Ne.symm i.property))
  have hrange : Set.range (fun i : Function.support b => w i.val) = w '' Function.support b := by
    ext x
    exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property, hi⟩,
      fun ⟨i, hi, hix⟩ => ⟨⟨i, hi⟩, hix⟩⟩
  rw [hbar, hrange] at hri
  refine ⟨convexHull ℝ (w '' Function.support b), (hS.image w).convexHull, ?_, hri⟩
  rw [convexHull_eq_toExposed w (Function.support b) hS ℓ
    (-f ((1 : ℝ), (0 : E))) hbound hvalue hstrict]
  exact ContinuousLinearMap.toExposed.isExposed


end GroupActions
end
