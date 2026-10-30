import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteCover

/-!
# Morphisms of finite intersection indices
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- A map of chart labels sends every nonempty finite index set to its image. -/
noncomputable def intersectionIndexMap {I J : Type u} (label : J → I) :
    {s : Finset J // s.Nonempty} ⥤ {s : Finset I // s.Nonempty} := by
  classical
  exact
    { obj := fun s ↦ ⟨s.val.image label, s.property.image label⟩
      map := fun f ↦ homOfLE (Finset.image_subset_image (leOfHom f)) }

/-- A morphism carrying each source chart into its labeled target chart also carries
every finite intersection into the corresponding intersection of target charts. -/
theorem intersection_preimage_le {X Y : Scheme.{u}} {I J : Type u}
    (f : X ⟶ Y) (U : J → X.Opens) (V : I → Y.Opens) (label : J → I)
    (hle : ∀ j, U j ≤ f ⁻¹ᵁ V (label j)) (s : {s : Finset J // s.Nonempty}ᵒᵖ) :
    (intersectionOpens U).obj s ≤
      f ⁻¹ᵁ (intersectionOpens V).obj ((intersectionIndexMap label).op.obj s) := by
  classical
  intro x hx
  change f x ∈ ⨅ i ∈ s.unop.val.image label, V i
  rw [← Finset.inf_eq_iInf]
  change f x ∈ (((s.unop.val.image label).inf V : Y.Opens) : Set Y)
  rw [TopologicalSpace.Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Set.iInf_eq_iInter, Set.mem_iInter]
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hUi : (intersectionOpens U).obj s ≤ U j :=
    iInf_le_of_le j (iInf_le _ hj)
  exact hle j (hUi hx)

end FrobeniusSplitting
