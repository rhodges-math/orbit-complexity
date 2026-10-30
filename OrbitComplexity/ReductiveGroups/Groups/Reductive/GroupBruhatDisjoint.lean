import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import Batteries.Tactic.Lint

/-!
# Weyl representatives in the Borel subgroup

Conjugation by a Borel point fixes the Borel defining ideal and tangent image.
A Weyl representative in the Borel therefore preserves positive root spaces,
so its inverse has no inversions and its Weyl element is the identity.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem borelIdeal_conjugate_le (g : G.points) (hg : g ∈ G.borelPoints) :
    G.borelIdeal.conjugate g ≤ G.borelIdeal := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  let : IsReduced G.borelAlgebra := isReduced_of_smooth K G.borelAlgebra
  let : IsReduced (CommHopfAlgCat.quotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal) :=
    inferInstanceAs (IsReduced G.borelAlgebra)
  apply HopfIdeal.le_of_quotientPointsSubgroup_le
    (H := CommHopfAlgCat.of K G.coordinateAlgebra) (K := K)
  intro b hb
  have hconj : g⁻¹ * b * g ∈ G.borelPoints :=
    G.borelPoints.mul_mem (G.borelPoints.mul_mem (G.borelPoints.inv_mem hg) hb) hg
  have h := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff
    G.borelIdeal g (CommAlgCat.of K K) (g⁻¹ * b * g)).mpr hconj
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
    AlgHom.mapValue_id, MonoidHom.id_apply, mul_assoc, mul_inv_cancel_left,
    mul_inv_cancel, mul_one] using h

omit [CharZero K] in
private theorem borelIdeal_conjugate_eq (g : G.points) (hg : g ∈ G.borelPoints) :
    G.borelIdeal.conjugate g = G.borelIdeal := by
  apply le_antisymm (G.borelIdeal_conjugate_le g hg)
  have h := HopfIdeal.conjugate_mono g (G.borelIdeal_conjugate_le g⁻¹
    (G.borelPoints.inv_mem hg))
  simpa using h

omit [CharZero K] in
/-- A Borel point preserves its tangent submodule under the adjoint representation. -/
theorem borelTangent_map_adjoint (g : G.points) (hg : g ∈ G.borelPoints) :
    G.borelTangent.toSubmodule.map (affineGroupAdjointRepresentation g) =
      G.borelTangent.toSubmodule := by
  have h := conjugate_tangentImage G.borelIdeal g
  rw [G.borelIdeal_conjugate_eq g hg] at h
  exact h.symm

/-- A Weyl representative preserving the Borel tangent has trivial Weyl element. -/
theorem eq_one_of_weylPoint_adjoint (w : G.weylGroup)
    (hB : G.borelTangent.toSubmodule.map
      (affineGroupAdjointRepresentation (G.weylPoint w)) = G.borelTangent.toSubmodule) :
    w = 1 := by
  have hpos (r : G.rootIndex) (hr : G.rootBase.IsPos r) :
      G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w r) := by
    apply (G.rootWeightSpace_le_borel _).mp
    rw [← G.weylPoint_rootWeightSpace w r]
    change (G.rootWeightSpace r).map
      (affineGroupAdjointRepresentation (G.weylPoint w)) ≤ G.borelTangent.toSubmodule
    exact (Submodule.map_mono ((G.rootWeightSpace_le_borel r).mpr hr)).trans hB.le
  have hempty : leftRootInversionIndices G.rootBase w⁻¹ = ∅ := by
    ext i
    simp only [mem_leftRootInversionIndices, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hi, hni⟩
    apply hni
    simpa only [inv_inv] using hpos i hi
  have hi : w⁻¹ = 1 := (rootInversionCount_eq_zero_iff G.rootBase w⁻¹).mp (by
    simp [rootInversionCount, leftRootInversions, hempty])
  exact inv_eq_one.mp hi

/-- A Weyl representative belongs to the chosen Borel only for the identity Weyl element. -/
theorem eq_one_of_weylPoint_mem_borel (w : G.weylGroup) (hw : G.weylPoint w ∈ G.borelPoints) :
    w = 1 :=
  G.eq_one_of_weylPoint_adjoint w (G.borelTangent_map_adjoint (G.weylPoint w) hw)

end ReductiveGroups.ReductiveGroupData
