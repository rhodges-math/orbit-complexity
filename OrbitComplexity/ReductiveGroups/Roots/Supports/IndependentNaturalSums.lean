import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Natural sums in an independent set

If a natural-coefficient combination of an independent set is again one
of its elements, its total multiplicity is one. The sum-of-coordinates
functional is constructed on the span of that independent set only.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {R M : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]

/-- The equality is

```lean
∑ δ ∈ t, n δ = 1
```
-/
theorem NatCoefficientSum.eq_one_of_linearIndepOn {S : Set M}
    (hS : LinearIndepOn R id S) (t : Finset S) (n : S → ℕ) {β : M} (hβ : β ∈ S)
    (hsum : ∑ δ ∈ t, n δ • (δ : M) = β) : ∑ δ ∈ t, n δ = 1 := by
  let v : S → M := fun δ => δ.val
  have hlin : LinearIndependent R v := hS
  let B := Module.Basis.span hlin
  have he : ∑ δ ∈ t, n δ • B δ = B ⟨β, hβ⟩ := by
    apply Subtype.ext
    simpa [B, v] using hsum
  have hh := congrArg B.sumCoords he
  simp only [map_sum, map_nsmul, Module.Basis.sumCoords_self_apply,
    nsmul_eq_mul, mul_one] at hh
  exact_mod_cast hh

end ReductiveGroups
