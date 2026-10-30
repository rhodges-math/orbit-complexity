import OrbitComplexity.ReductiveGroups.RootClosure.Basic
import Mathlib.Algebra.Group.Submonoid.Operations

/-!
# Transport of auxiliary closure

An additive equivalence carries the closure of a set under natural-number linear
combinations to the corresponding closure of its image.
-/

namespace ReductiveGroups

variable {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]

/-- Auxiliary closure commutes with transport of all three sets along an
additive equivalence. -/
theorem image_auxiliaryClosure (e : V ≃+ W) (A U R : Set V) :
    e '' auxiliaryClosure A U R = auxiliaryClosure (e '' A) (e '' U) (e '' R) := by
  have hspan :
      e '' (AddSubmonoid.closure (A ∪ R) : Set V) =
        (AddSubmonoid.closure (e '' A ∪ e '' R) : Set W) := by
    simpa only [AddSubmonoid.coe_map, AddEquiv.coe_toAddMonoidHom, Set.image_union] using
      congrArg (fun S : AddSubmonoid W => (S : Set W))
        (AddMonoidHom.map_mclosure e.toAddMonoidHom (A ∪ R))
  unfold auxiliaryClosure
  rw [Set.image_inter e.injective, hspan]

/-- Membership version of additive-equivariant transport. -/
theorem apply_mem_auxiliaryClosure_image_iff (e : V ≃+ W) (A U R : Set V) (β : V) :
    e β ∈ auxiliaryClosure (e '' A) (e '' U) (e '' R) ↔
      β ∈ auxiliaryClosure A U R := by
  rw [← image_auxiliaryClosure]
  exact e.injective.mem_set_image

end ReductiveGroups
