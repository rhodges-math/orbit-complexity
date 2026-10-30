import OrbitComplexity.BruhatIntervals.Realizations.Geometric

/-!
# Root cones and invariant forms

The geometric action distinguishes the simple generators. In every realization the positive cone
is closed under nonnegative linear combinations, and the action preserves the geometric form.

## Main results

* `simple_injective`: distinct simple indices give distinct simple generators.
* `Realization.positiveCone_neg_eq_zero`: the positive cone contains no nonzero vector and its
  negative.
* `Realization.action_form`: the geometric form is invariant under the whole Coxeter action.
* `Realization.form_root_eq_one`: every root has squared length one.

## Implementation notes

The cone calculations use the independence of the simple roots and allow additional ambient
directions outside their span.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Chapter 4.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- Distinct simple indices give distinct simple generators. -/
theorem simple_injective : Function.Injective cs.simple := by
  intro i j hij
  by_contra hne
  have hroot := congrArg (fun element : W =>
    geometricAction matrix cs element (geometricRoot i)) hij
  rw [geometricAction_simple, geometricAction_simple, geometricReflection_root_self,
    geometricReflection_apply] at hroot
  have hcoord := congrArg (fun vector : Index →₀ ℝ => vector i) hroot
  simp only [geometricRoot, Finsupp.neg_apply, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_zero, sub_zero] at hcoord
  linarith

namespace Realization

variable {cs} {V : Type*} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- The positive cone is closed under addition. -/
theorem positiveCone_add {x y : V}
    (hx : x ∈ realization.positiveCone) (hy : y ∈ realization.positiveCone) :
    x + y ∈ realization.positiveCone := by
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨g, hg, hgy⟩ := hy
  refine ⟨f + g, fun i => ?_, ?_⟩
  · exact add_nonneg (hf i) (hg i)
  · rw [map_add, hfx, hgy]

/-- The positive cone is closed under multiplication by nonnegative real scalars. -/
theorem positiveCone_smul {x : V} {c : ℝ}
    (hc : 0 ≤ c) (hx : x ∈ realization.positiveCone) :
    c • x ∈ realization.positiveCone := by
  obtain ⟨f, hf, hfx⟩ := hx
  refine ⟨c • f, fun i => ?_, ?_⟩
  · exact mul_nonneg hc (hf i)
  · rw [map_smul, hfx]

/-- A vector and its negative can both belong to the positive cone only when they vanish. -/
theorem positiveCone_neg_eq_zero {x : V}
    (hx : x ∈ realization.positiveCone) (hneg : -x ∈ realization.positiveCone) : x = 0 := by
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨g, hg, hgx⟩ := hneg
  have hsum : f + g = 0 := realization.root_independent (by
    rw [map_add, hfx, hgx, map_zero, add_neg_cancel])
  have hfzero : f = 0 := by
    ext i
    have hcoord := congrArg (fun coefficients : Index →₀ ℝ => coefficients i) hsum
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at hcoord ⊢
    have hfi := hf i
    have hgi := hg i
    linarith
  rw [hfzero, map_zero] at hfx
  exact hfx.symm

/-- A positive root cannot have its negative among the positive roots. -/
theorem positiveRoots_ne_neg {x : V} (hx : x ∈ realization.positiveRoots)
    (hneg : -x ∈ realization.positiveRoots) : False :=
  realization.root_ne_zero hx.1 (realization.positiveCone_neg_eq_zero hx.2 hneg.2)

/-- Each simple generator preserves the geometric form. -/
theorem action_simple_form (i : Index) (x y : V) :
    realization.form (realization.action (cs.simple i) x)
      (realization.action (cs.simple i) y) = realization.form x y := by
  simp only [realization.action_simple, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, realization.form_root_self]
  rw [realization.form_isSymm.eq x (realization.simpleRoot i)]
  ring

/-- The Coxeter action preserves the geometric form. -/
theorem action_form (w : W) (x y : V) :
    realization.form (realization.action w x) (realization.action w y) =
      realization.form x y := by
  suffices h : ∀ w : W, ∀ x y : V,
      realization.form (realization.action w x) (realization.action w y) =
        realization.form x y from h w x y
  intro w
  apply cs.simple_induction_right w
  · intro x y
    rw [map_one]
    rfl
  · intro v i ih x y
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih,
      realization.action_simple_form]

/-- Every root has squared length one in the geometric form. -/
theorem form_root_eq_one {x : V} (hx : x ∈ realization.roots) :
    realization.form x x = 1 := by
  obtain ⟨w, i, rfl⟩ := hx
  rw [realization.action_form, realization.form_root_self]

end Realization

end BruhatIntervals
