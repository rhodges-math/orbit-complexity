import OrbitComplexity.BruhatIntervals.Order.Basic
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.SpanEquality

/-!
# Refining long Bruhat edges

Every directed Bruhat edge of length greater than one admits a directed three-edge path with the
same endpoints. The reflections of that path generate a dihedral reflection subgroup.

## Main results

* `long_edge_path`: a long edge has a directed three-edge refinement with a dihedral certificate.

## Implementation notes

The proof uses induction on the upper endpoint's length, a left descent, and the three path
cases in the Bruhat-graph reconstruction argument. The four-reflection product theorem supplies
the resulting dihedral subgroup.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  proof of Proposition 3.3, claim (i).
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

private theorem step_mul_simple {u v : W} (hstep : cs.BruhatStep u v) (i : Index)
    (hne : v ≠ u * cs.simple i) : cs.BruhatStep (u * cs.simple i) (v * cs.simple i) := by
  have huv := hstep.bruhatLE
  obtain ⟨t, ht, htarget, hlt⟩ := hstep
  have htarget' : v * cs.simple i = t * (u * cs.simple i) := by rw [htarget, mul_assoc]
  refine ⟨t, ht, htarget', ?_⟩
  by_contra hnot
  have hlengthne : cs.length (v * cs.simple i) ≠ cs.length (u * cs.simple i) := by
    rw [htarget']
    exact ht.length_mul_right_ne _
  have hshort : cs.length (v * cs.simple i) < cs.length (u * cs.simple i) := by omega
  have hu : ¬cs.IsRightDescent u i := by
    intro hdesc
    have hulen := cs.isRightDescent_iff.mp hdesc
    rcases cs.length_mul_simple v i with hvlen | hvlen <;> omega
  have hulen := cs.not_isRightDescent_iff.mp hu
  have hle := bruhatLE_mul_of_ascent cs huv i hu
  have heq : u = v * cs.simple i := by
    by_contra hneq
    have hstrict := hle.length_lt_of_ne hneq
    omega
  apply hne
  have heq' := congrArg (· * cs.simple i) heq
  simpa only [cs.simple_mul_simple_cancel_right] using heq'.symm

private theorem simple_mul_step {u v : W} (hstep : cs.BruhatStep u v) (i : Index)
    (hne : v ≠ cs.simple i * u) : cs.BruhatStep (cs.simple i * u) (cs.simple i * v) := by
  have hinv : v⁻¹ ≠ u⁻¹ * cs.simple i := by
    intro heq
    apply hne
    simpa only [inv_inv, mul_inv_rev, cs.inv_simple] using congrArg Inv.inv heq
  have h := (step_mul_simple cs hstep.inv i hinv).inv
  simpa only [mul_inv_rev, inv_inv, cs.inv_simple] using h

private theorem three_edge_path {x y : W} (hstep : cs.BruhatStep x y)
    (hgap : cs.length x + 1 < cs.length y) :
    ∃ a b : W, cs.BruhatStep x a ∧ cs.BruhatStep a b ∧ cs.BruhatStep b y := by
  suffices aux : ∀ n : ℕ, ∀ x y : W, cs.length y = n → cs.BruhatStep x y →
      cs.length x + 1 < cs.length y →
      ∃ a b : W, cs.BruhatStep x a ∧ cs.BruhatStep a b ∧ cs.BruhatStep b y by
    exact aux (cs.length y) x y rfl hstep hgap
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hlength hstep hgap
    have hyne : y ≠ 1 := by
      intro heq
      rw [heq, cs.length_one] at hgap
      omega
    obtain ⟨i, hiy⟩ := cs.exists_leftDescent_of_ne_one hyne
    have hylen := cs.isLeftDescent_iff.mp hiy
    have hne : y ≠ cs.simple i * x := by
      intro heq
      rcases cs.length_simple_mul x i with hxlen | hxlen <;> rw [heq] at hgap <;> omega
    have hstep' := simple_mul_step cs hstep i hne
    have hlast : cs.BruhatStep (cs.simple i * y) y := by
      have hlt : cs.length (cs.simple i * y) <
          cs.length (cs.simple i * (cs.simple i * y)) := by
        rw [cs.simple_mul_simple_cancel_left]
        omega
      simpa only [cs.simple_mul_simple_cancel_left] using cs.bruhatStep_simple_mul i hlt
    by_cases hix : cs.IsLeftDescent x i
    · have hxlen := cs.isLeftDescent_iff.mp hix
      obtain ⟨a, b, hfirst, hmiddle, hthird⟩ :=
        ih (cs.length (cs.simple i * y)) (by omega)
          (cs.simple i * x) (cs.simple i * y) rfl hstep' (by omega)
      by_cases hax : a = x
      · exact ⟨b, cs.simple i * y, hax ▸ hmiddle, hthird, hlast⟩
      have hfirst' : cs.BruhatStep x (cs.simple i * a) := by
        have h := simple_mul_step cs hfirst i (by
          simpa only [cs.simple_mul_simple_cancel_left] using hax)
        simpa only [cs.simple_mul_simple_cancel_left] using h
      by_cases hab : cs.simple i * a = b
      · exact ⟨b, cs.simple i * y, hab ▸ hfirst', hthird, hlast⟩
      have hmiddle' := simple_mul_step cs hmiddle i (Ne.symm hab)
      have hthird' : cs.BruhatStep (cs.simple i * b) y := by
        have hneq : cs.simple i * y ≠ cs.simple i * b := by
          intro heq
          have hback := mul_left_cancel heq
          have hlt := hthird.length_lt
          rw [← hback] at hlt
          omega
        simpa only [cs.simple_mul_simple_cancel_left] using
          simple_mul_step cs hthird i hneq
      exact ⟨cs.simple i * a, cs.simple i * b, hfirst', hmiddle', hthird'⟩
    · have hxlen := cs.not_isLeftDescent_iff.mp hix
      exact ⟨cs.simple i * x, cs.simple i * y,
        cs.bruhatStep_simple_mul i (by omega), hstep', hlast⟩

private theorem step_reflection {x y : W} (hstep : cs.BruhatStep x y) :
    cs.IsReflection (y * x⁻¹) := by
  obtain ⟨t, ht, rfl, _⟩ := hstep
  simpa only [mul_inv_cancel_right] using ht

/-- Every long directed Bruhat edge has a directed three-edge refinement whose reflections
generate a dihedral subgroup. -/
theorem long_edge_path (x y : W) (hstep : cs.BruhatStep x y)
    (hgap : cs.length x + 1 < cs.length y) :
    ∃ a b : W, cs.BruhatStep x a ∧ cs.BruhatStep a b ∧ cs.BruhatStep b y ∧
      ∃ n : ℕ, Nonempty (DihedralGroup n ≃*
        Subgroup.closure ({a * x⁻¹, b * a⁻¹, y * b⁻¹} : Set W)) := by
  obtain ⟨a, b, hfirst, hmiddle, hlast⟩ := three_edge_path cs hstep hgap
  let p := a * x⁻¹
  let q := b * a⁻¹
  let r := y * b⁻¹
  let t := y * x⁻¹
  have hp : cs.IsReflection p := step_reflection cs hfirst
  have hq : cs.IsReflection q := step_reflection cs hmiddle
  have hr : cs.IsReflection r := step_reflection cs hlast
  have ht : cs.IsReflection t := step_reflection cs hstep
  have hlong : t = r * q * p := by dsimp only [t, r, q, p]; group
  have hprod : t * p = r * q := by rw [hlong, mul_assoc, hp.mul_self, mul_one]
  have hne : t * p ≠ 1 := by
    intro heq
    have heqt : t = p := mul_right_cancel (heq.trans hp.mul_self.symm)
    have hya : y = a := by
      have h := congrArg (· * x) heqt
      simpa only [t, p, inv_mul_cancel_right] using h
    have hlt := hmiddle.length_lt.trans hlast.length_lt
    rw [hya] at hlt
    exact Nat.lt_irrefl _ hlt
  obtain ⟨n, ⟨equivalence⟩⟩ := reflectionProduct_dihedral cs ht hp hr hq hprod hne
  let K := Subgroup.closure ({p, q, r} : Set W)
  have hpK : p ∈ K := Subgroup.subset_closure (Or.inl rfl)
  have hqK : q ∈ K := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hrK : r ∈ K := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hgroup : Subgroup.closure ({t, p, r, q} : Set W) = K := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro g hg
      rcases hg with rfl | rfl | rfl | rfl
      · rw [hlong]
        exact K.mul_mem (K.mul_mem hrK hqK) hpK
      · exact hpK
      · exact hrK
      · exact hqK
    · apply Subgroup.closure_mono
      intro g hg
      rcases hg with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
  exact ⟨a, b, hfirst, hmiddle, hlast, n,
    ⟨equivalence.trans (MulEquiv.subgroupCongr hgroup)⟩⟩

end BruhatIntervals
