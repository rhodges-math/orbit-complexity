import OrbitComplexity.BruhatIntervals.Permutations.Realization

/-!
# Permutations in the interval examples

The coordinate permutations below specify the one-line permutations used for the interval
span calculation and the two Boolean intervals.
-/

namespace SchubertOrbits.BruhatExamples

/-- The one-line permutation `1324` interchanges the middle coordinates. -/
def lower1324 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- The one-line permutation `3412` exchanges the first two coordinates with the last two. -/
def upper3412 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The one-line permutation `3142` is obtained by interchanging the middle positions of `3412`. -/
def upper3142 : Equiv.Perm (Fin 4) := upper3412 * Equiv.swap 1 2

/-- The one-line permutation `4231` exchanges the first and last coordinates. -/
def upper4231 : Equiv.Perm (Fin 4) := Equiv.swap 0 3

/-- The one-line permutation `51234` moves each coordinate one position around the cycle. -/
def upper51234 : Equiv.Perm (Fin 5) :=
  Equiv.swap 3 4 * Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1

/-- The coordinate values of `1324`, with coordinate indices starting at zero. -/
theorem lower1324_apply : ∀ i : Fin 4,
    lower1324 i = (if i = 1 then 2 else if i = 2 then 1 else i) := by decide

/-- The coordinate values of `3412`, with coordinate indices starting at zero. -/
theorem upper3412_apply : ∀ i : Fin 4,
    upper3412 i = (if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1) := by decide

/-- The coordinate values of `3142`, with coordinate indices starting at zero. -/
theorem upper3142_apply : ∀ i : Fin 4,
    upper3142 i = (if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3 else 1) := by decide

/-- The coordinate values of `4231`, with coordinate indices starting at zero. -/
theorem upper4231_apply : ∀ i : Fin 4,
    upper4231 i = (if i = 0 then 3 else if i = 3 then 0 else i) := by decide

/-- The coordinate values of `51234`, with coordinate indices starting at zero. -/
theorem upper51234_apply : ∀ i : Fin 5,
    upper51234 i = (if i = 0 then 4 else i - 1) := by decide

end SchubertOrbits.BruhatExamples
