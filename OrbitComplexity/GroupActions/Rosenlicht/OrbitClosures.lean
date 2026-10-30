import OrbitComplexity.GroupActions.Actions.LocallyClosed
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Containment and equality of algebraic-group orbit closures
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

/-- Two algebraic-group orbits with the same closure are the same orbit. -/
theorem mem_orbit_of_orbitClosure_eq {K : Type u} [Field K] [IsAlgClosed K]
    (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    (x y : X.points) (h : orbitClosure H X x = orbitClosure H X y) :
    y ∈ MulAction.orbit H.points x := by
  have hc : closure (MulAction.orbit H.points x) = closure (MulAction.orbit H.points y) := by
    rw [X.isEmbedding_pointMap.closure_eq_preimage_closure_image,
      X.isEmbedding_pointMap.closure_eq_preimage_closure_image]
    change X.pointMap ⁻¹' orbitClosure H X x = X.pointMap ⁻¹' orbitClosure H X y
    rw [h]
  have hx : x ∈ MulAction.orbit H.points x := MulAction.mem_orbit_self x
  obtain ⟨W, hW, hWs⟩ := isLocallyClosedAt_iff_exists_inter_closure_subset.mp
    ((isLocallyClosed_iff_isLocallyClosedAt.mp (orbit_locallyClosed H X x)) x hx)
  have hxc : x ∈ closure (MulAction.orbit H.points y) := hc ▸ subset_closure hx
  obtain ⟨z, hzW, hzy⟩ := (mem_closure_iff_nhds.mp hxc) W hW
  have hzs : z ∈ MulAction.orbit H.points x :=
    hWs ⟨hzW, hc.symm ▸ subset_closure hzy⟩
  exact MulAction.mem_orbit_trans (MulAction.mem_orbit_symm.mp hzy) hzs

end

end GroupActions

open CategoryTheory AlgebraicGeometry Topology
open scoped Pointwise

namespace GroupActions

noncomputable section

universe u

/-- An orbit closure contains every orbit whose initial point it contains. -/
theorem orbitClosure_le_of_mem {K : Type u} [Field K] [IsAlgClosed K]
    (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    (x y : X.points) (hxy : X.pointMap x ∈ orbitClosure H X y) :
    orbitClosure H X x ⊆ orbitClosure H X y := by
  let : ContinuousConstSMul H.points X.points :=
    ⟨fun h ↦ by
      rw [show (fun z : X.points ↦ h • z) =
        Variety.mapPoints (Variety.translateMorphism H X h) from
          funext fun z ↦ (Variety.mapPoints_translateMorphism H X h z).symm]
      exact Variety.continuous_mapPoints (Variety.translateMorphism H X h)⟩
  have hx : x ∈ closure (MulAction.orbit H.points y) := by
    rw [X.isEmbedding_pointMap.closure_eq_preimage_closure_image]
    exact hxy
  change closure (X.pointMap '' MulAction.orbit H.points x) ⊆
    closure (X.pointMap '' MulAction.orbit H.points y)
  apply closure_minimal ?_ isClosed_closure
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hz
  have hh : h • x ∈ closure (MulAction.orbit H.points y) :=
    smul_closure_orbit_subset h y ⟨x, hx, rfl⟩
  rw [X.isEmbedding_pointMap.closure_eq_preimage_closure_image] at hh
  exact hh

/-- Mutual containment of two rational points in each other's orbit closures
puts them in the same algebraic-group orbit. -/
theorem mem_orbit_of_mutual_closure {K : Type u} [Field K] [IsAlgClosed K]
    (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    (x y : X.points) (hxy : X.pointMap x ∈ orbitClosure H X y)
    (hyx : X.pointMap y ∈ orbitClosure H X x) : y ∈ MulAction.orbit H.points x := by
  apply mem_orbit_of_orbitClosure_eq H X x y
  exact Set.Subset.antisymm (orbitClosure_le_of_mem H X x y hxy)
    (orbitClosure_le_of_mem H X y x hyx)

end

end GroupActions
