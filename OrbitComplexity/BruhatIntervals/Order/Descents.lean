import OrbitComplexity.BruhatIntervals.Order.Basic

/-!
# Descent sets

The left and right descent sets consist of the simple indices whose left or right multiplication
decreases Coxeter length.

## Main definitions

* `leftDescents`: the simple left descents.
* `rightDescents`: the simple right descents.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 1.4.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- The simple indices whose left multiplication decreases Coxeter length. -/
def leftDescents (w : W) : Set Index := {i | cs.IsLeftDescent w i}

/-- The simple indices whose right multiplication decreases Coxeter length. -/
def rightDescents (w : W) : Set Index := {i | cs.IsRightDescent w i}

/-- A simple index is a left descent exactly when its left multiplication decreases length. -/
theorem mem_leftDescents (w : W) (i : Index) :
    i ∈ leftDescents cs w ↔ cs.length (cs.simple i * w) < cs.length w := Iff.rfl

/-- A simple index is a right descent exactly when its right multiplication decreases length. -/
theorem mem_rightDescents (w : W) (i : Index) :
    i ∈ rightDescents cs w ↔ cs.length (w * cs.simple i) < cs.length w := Iff.rfl

end BruhatIntervals
