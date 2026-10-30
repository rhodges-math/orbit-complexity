import OrbitComplexity.ReductiveGroups.Lie.Roots.TripleBondRootExpressionNonvanishing

/-!
# Canonical Root Weight Realization

The realization interface is constructed for Mathlib's root
system of a split IsKilling Lie algebra. For a reductive algebraic group the
corresponding system is the root system of the center quotient of its
tangent algebra (`Groups/ReductiveCharacterRoots.lean`). -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

omit [CharZero K] [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
    [H.IsCartanSubalgebra] [IsTriangularizable K H L] in
/-- Evaluate a linear functional on the Cartan subalgebra. -/
def cartanDualEvaluation : Module.Dual K H →+ (H → K) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The abstract root vector in the canonical Lie root system is
its nonzero Lie weight under evaluation. -/
theorem canonicalRootWeight_realization (ξ : H.root) :
    ((ξ : Weight K H L) : H → K) =
      cartanDualEvaluation H ((rootSystem H).root ξ) ∧
      (ξ : Weight K H L).IsNonZero := by
  refine ⟨rfl, ?_⟩
  exact (Finset.mem_filter.mp ξ.property).2

/-- In the canonical split semisimple root system, both the additive
realization and nonzero root vectors exist; neither is assumed. -/
theorem CanonicalRootWeight.realization_and_vectors :
    ∃ (Φ : Module.Dual K H →+ (H → K))
      (ρ : H.root → Weight K H L) (e : H.root → L),
      (∀ ξ, (ρ ξ : H → K) = Φ ((rootSystem H).root ξ)) ∧
      (∀ ξ, (ρ ξ).IsNonZero) ∧
      (∀ ξ, e ξ ∈ rootSpace H (ρ ξ) ∧ e ξ ≠ 0) := by
  let ρ : H.root → Weight K H L := fun ξ => ξ.val
  obtain ⟨e, he⟩ := exists_nonzero_root_vectors_for_weights ρ
  refine ⟨cartanDualEvaluation H, ρ, e, ?_, ?_, he⟩
  · intro ξ
    exact (canonicalRootWeight_realization H ξ).1
  · intro ξ
    exact (canonicalRootWeight_realization H ξ).2

end ReductiveGroups
