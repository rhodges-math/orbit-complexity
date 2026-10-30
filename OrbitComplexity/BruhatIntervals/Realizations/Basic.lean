import OrbitComplexity.BruhatIntervals.Realizations.Form
import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Realizations of Coxeter systems

A realization consists of independent simple roots, their geometric bilinear form, and an action
whose simple generators act by the corresponding reflections. Its roots are the translates of the
simple roots, and its positive roots lie in the cone of nonnegative simple-root combinations.

## Main definitions

* `Realization`: the geometric data and action of a Coxeter system.
* `Realization.roots`: translates of simple roots under the Coxeter group.
* `Realization.positiveCone`: nonnegative linear combinations of simple roots.
* `Realization.positiveRoots`: roots in the positive cone.

## Main results

* `Realization.root_ne_zero`: roots are nonzero.
* `Realization.action_mem_roots`: the Coxeter action preserves roots.
* `Realization.simpleRoot_mem_positiveRoots`: simple roots are positive.

## Implementation notes

The real vector space may contain directions outside the span of the roots. Simple roots have
squared length one. Rescaling root vectors by positive real numbers preserves their spans.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Chapter 4.
-/

namespace BruhatIntervals

variable {S W V : Type*} [Group W] {M : CoxeterMatrix S}
  (cs : CoxeterSystem M W) [AddCommGroup V] [Module ℝ V]

/-- A geometric realization of a Coxeter system by simple-root reflections on a real vector space.
The simple roots are independent and their pairings are prescribed by the Coxeter matrix. -/
structure Realization where
  /-- The simple roots. -/
  simpleRoot : S → V
  /-- The simple roots are linearly independent. -/
  root_independent : LinearIndependent ℝ simpleRoot
  /-- The geometric bilinear form. -/
  form : LinearMap.BilinForm ℝ V
  /-- The geometric form is symmetric. -/
  form_isSymm : form.IsSymm
  /-- Pairings of simple roots are the cosine Gram entries. -/
  form_root : ∀ i j, form (simpleRoot i) (simpleRoot j) =
    -Real.cos (Real.pi / (M i j : ℝ))
  /-- The linear action of the Coxeter group. -/
  action : W →* (V ≃ₗ[ℝ] V)
  /-- Each simple generator acts by reflection in its simple root. -/
  action_simple : ∀ i x, action (cs.simple i) x =
    x - (2 * form (simpleRoot i) x) • simpleRoot i

namespace Realization

variable {cs} (realization : Realization cs (V := V))

/-- Every simple root in a realization is nonzero. -/
theorem simpleRoot_ne_zero (i : S) : realization.simpleRoot i ≠ 0 :=
  realization.root_independent.ne_zero i

/-- A simple root has squared length one. -/
theorem form_root_self (i : S) :
    realization.form (realization.simpleRoot i) (realization.simpleRoot i) = 1 := by
  rw [realization.form_root, M.diagonal]
  simp only [Nat.cast_one, div_one, Real.cos_pi, neg_neg]

/-- A simple generator sends its simple root to its negative. -/
theorem action_simple_root (i : S) :
    realization.action (cs.simple i) (realization.simpleRoot i) =
      -realization.simpleRoot i := by
  rw [realization.action_simple, realization.form_root_self, mul_one]
  module

/-- The roots of a realization are all group translates of simple roots. -/
def roots : Set V :=
  {x | ∃ w : W, ∃ i : S, realization.action w (realization.simpleRoot i) = x}

/-- Membership in the root set is being a translate of a simple root. -/
theorem mem_roots {x : V} :
    x ∈ realization.roots ↔
      ∃ w : W, ∃ i : S, realization.action w (realization.simpleRoot i) = x := Iff.rfl

/-- Every simple root belongs to the root set. -/
theorem simpleRoot_mem_roots (i : S) : realization.simpleRoot i ∈ realization.roots := by
  exact ⟨1, i, by rw [map_one]; rfl⟩

/-- Every root is nonzero. -/
theorem root_ne_zero {x : V} (h : x ∈ realization.roots) : x ≠ 0 := by
  obtain ⟨w, i, rfl⟩ := h
  intro hzero
  apply realization.simpleRoot_ne_zero i
  apply (realization.action w).injective
  simpa only [map_zero] using hzero

/-- Applying a group element to a root gives another root. -/
theorem action_mem_roots (w : W) {x : V} (h : x ∈ realization.roots) :
    realization.action w x ∈ realization.roots := by
  obtain ⟨v, i, rfl⟩ := h
  refine ⟨w * v, i, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply]

/-- Negating a root gives another root. -/
theorem neg_mem_roots {x : V} (h : x ∈ realization.roots) : -x ∈ realization.roots := by
  obtain ⟨w, i, rfl⟩ := h
  refine ⟨w * cs.simple i, i, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, realization.action_simple_root, map_neg]

/-- The positive cone consists of finite nonnegative linear combinations of simple roots. -/
def positiveCone : Set V :=
  {x | ∃ coefficients : S →₀ ℝ, (∀ i, 0 ≤ coefficients i) ∧
    Finsupp.linearCombination ℝ realization.simpleRoot coefficients = x}

/-- Positive roots are the roots belonging to the positive cone. -/
def positiveRoots : Set V := realization.roots ∩ realization.positiveCone

/-- A positive root is a root with nonnegative simple-root coordinates. -/
theorem mem_positiveRoots {x : V} :
    x ∈ realization.positiveRoots ↔ x ∈ realization.roots ∧
      ∃ coefficients : S →₀ ℝ, (∀ i, 0 ≤ coefficients i) ∧
        Finsupp.linearCombination ℝ realization.simpleRoot coefficients = x := Iff.rfl

/-- Every simple root is positive. -/
theorem simpleRoot_mem_positiveRoots (i : S) :
    realization.simpleRoot i ∈ realization.positiveRoots := by
  classical
  refine ⟨realization.simpleRoot_mem_roots i, Finsupp.single i 1, ?_, ?_⟩
  · intro j
    by_cases hij : i = j
    · subst j
      simp only [Finsupp.single_eq_same, zero_le_one]
    · exact le_of_eq (Finsupp.single_eq_of_ne (Ne.symm hij)).symm
  · simp only [Finsupp.linearCombination_single, one_smul]

end Realization

end BruhatIntervals
