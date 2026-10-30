import Mathlib.Algebra.Lie.Extension

/-!
# Central Extension Cocycle

A central Lie extension has trivial kernel action. Its linear
section defect therefore satisfies the central cocycle identity. -/

noncomputable section
namespace ReductiveGroups

variable {K N S : Type*} [Field K] [LieRing N] [LieAlgebra K N]
  [LieRing S] [LieAlgebra K S]

/-- A central extension has abelian kernel, derived from injectivity of
the inclusion rather than as an extra hypothesis. -/
theorem centralExtension_isLieAbelian (E : LieAlgebra.Extension K N S)
    (hc : ∀ (x : E.L) (z : N), ⁅x, E.incl z⁆ = 0) : IsLieAbelian N := by
  constructor
  intro x y
  apply E.incl_injective
  rw [map_zero, LieHom.map_lie]
  exact hc (E.incl x) y

/-- The action on the kernel constructed from a central extension
is trivial. This applies to the library's own extension module structure. -/
theorem centralExtension_isTrivial [IsLieAbelian N]
    (E : LieAlgebra.Extension K N S)
    (hc : ∀ (x : E.L) (z : N), ⁅x, E.incl z⁆ = 0) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    LieModule.IsTrivial S N := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  constructor
  intro x z
  obtain ⟨y, rfl⟩ := E.proj_surjective x
  rw [E.ringModuleOf_bracket_proj]
  have hz : ⁅y, E.toKer z⁆ = 0 := by
    apply Subtype.ext
    change ⁅y, (E.toKer z : E.L)⁆ = 0
    rw [E.lie_toKer_apply]
    exact hc y z
  rw [hz, map_zero]

/-- The defect cocycle of any linear section of a central extension
satisfies the central (trivial-module) cocycle identity. -/
theorem centralExtension_twoCocycle_identity [IsLieAbelian N]
    (E : LieAlgebra.Extension K N S)
    (hc : ∀ (x : E.L) (z : N), ⁅x, E.incl z⁆ = 0)
    (s : S →ₗ[K] E.L) (hs : Function.LeftInverse E.proj s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    ∀ x y z : S,
      (E.twoCocycleOf hs).val x ⁅y, z⁆ =
        (E.twoCocycleOf hs).val ⁅x, y⁆ z +
          (E.twoCocycleOf hs).val y ⁅x, z⁆ := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  let := centralExtension_isTrivial E hc
  exact (LieModule.Cohomology.mem_twoCocycle_iff_of_trivial K S N
    (E.twoCocycleOf hs).val).mp (E.twoCocycleOf hs).property

end ReductiveGroups
