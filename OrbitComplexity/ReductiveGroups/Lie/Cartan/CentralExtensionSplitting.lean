import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralExtensionCocycle
import OrbitComplexity.ReductiveGroups.Lie.Cartan.KillingVectorCocycle
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Central Extension Splitting

A finite-dimensional central extension of a Killing Lie algebra has a
Lie-algebra section. The sign of the correction follows the defect
`[s x,s y] - s [x,y]`. -/

noncomputable section
namespace ReductiveGroups

variable {K N S : Type*} [Field K] [LieRing N] [LieAlgebra K N]
  [LieRing S] [LieAlgebra K S]

/-- Adding a primitive of the positive section defect corrects a linear
section to a Lie-algebra section. -/
theorem centralExtension_section_of_defect
    (E : LieAlgebra.Extension K N S)
    (hc : ∀ (x : E.L) (z : N), ⁅x, E.incl z⁆ = 0)
    (s : S →ₗ[K] E.L) (hs : Function.LeftInverse E.proj s)
    (f : S →ₗ[K] N)
    (hf : ∀ x y : S, E.incl (f ⁅x, y⁆) = ⁅s x, s y⁆ - s ⁅x, y⁆) :
    ∃ t : S →ₗ⁅K⁆ E.L, Function.LeftInverse E.proj t := by
  have hc' (z : N) (x : E.L) : ⁅E.incl z, x⁆ = 0 := by
    rw [← lie_skew, hc, neg_zero]
  let t : S →ₗ⁅K⁆ E.L := {
    toLinearMap := s + E.incl.toLinearMap.comp f
    map_lie' := by
      intro x y
      change s ⁅x, y⁆ + E.incl (f ⁅x, y⁆) =
        ⁅s x + E.incl (f x), s y + E.incl (f y)⁆
      rw [hf]
      simp only [add_lie, lie_add, hc, hc', add_zero]
      abel
  }
  refine ⟨t, ?_⟩
  intro x
  change E.proj (s x + E.incl (f x)) = x
  rw [map_add, E.proj_incl, add_zero, hs]

/-- A central extension with finite-dimensional kernel and Killing quotient
splits by a Lie homomorphism. -/
theorem centralExtension_exists_lieSection
    [FiniteDimensional K N] [FiniteDimensional K S] [LieAlgebra.IsKilling K S]
    (E : LieAlgebra.Extension K N S)
    (hc : ∀ (x : E.L) (z : N), ⁅x, E.incl z⁆ = 0) :
    ∃ t : S →ₗ⁅K⁆ E.L, Function.LeftInverse E.proj t := by
  let := centralExtension_isLieAbelian E hc
  let := E.ringModuleOf
  let := E.lieModuleOf
  obtain ⟨s, hs⟩ := E.proj.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr E.proj_surjective)
  have hs' : Function.LeftInverse E.proj s := by
    intro x
    exact LinearMap.congr_fun hs x
  let ω := (E.twoCocycleOf hs').val
  have hAlt : ∀ x : S, ω.val x x = 0 := ω.property
  have hId := centralExtension_twoCocycle_identity E hc s hs'
  have hCyc (x y z : S) :
      ω.val ⁅x, y⁆ z + ω.val ⁅y, z⁆ x + ω.val ⁅z, x⁆ y = 0 := by
    have h := hId x y z
    change ω x ⁅y, z⁆ = ω ⁅x, y⁆ z + ω y ⁅x, z⁆ at h
    have h₁ := LieModule.Cohomology.twoCochain_skew ω x ⁅y, z⁆
    have h₂ := LieModule.Cohomology.twoCochain_skew ω y ⁅x, z⁆
    change ω ⁅x, y⁆ z + ω ⁅y, z⁆ x + ω ⁅z, x⁆ y = 0
    rw [← h₁, ← lie_skew z x, map_neg, LinearMap.neg_apply, ← h₂]
    rw [h]
    abel
  obtain ⟨f, hf⟩ := killing_vector_cocycle_is_coboundary ω.val hAlt hCyc
  apply centralExtension_section_of_defect E hc s hs' f
  intro x y
  rw [← hf]
  have h := E.toKer.apply_symm_apply
    (⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs'.eq]⟩ : E.proj.ker)
  exact congrArg (fun z : E.proj.ker => (z : E.L)) h

end ReductiveGroups
