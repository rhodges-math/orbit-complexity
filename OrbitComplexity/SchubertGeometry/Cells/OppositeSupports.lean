import OrbitComplexity.SchubertGeometry.Cells.OppositeClosure
import OrbitComplexity.GroupActions.Varieties.ClosedPoints
import OrbitComplexity.GroupActions.Varieties.OpenPoints
import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.FiniteWeyl
import Batteries.Tactic.Lint

/-! # Supports of opposite Schubert varieties

Opposite Schubert supports are the unions of the cells above their indices
in Bruhat order. Their intersections are unions of the supports indexed by
common upper bounds.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology

namespace SchubertGeometry

universe u

private theorem constructible_points_eq {K : Type u} [Field K] [IsAlgClosed K]
    (X : GroupActions.Variety K) {S T : Set X.scheme}
    (hS : IsConstructible S) (hT : IsConstructible T)
    (hpoints : X.pointMap ⁻¹' S = X.pointMap ⁻¹' T) : S = T := by
  let : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  apply GroupActions.constructible_eq hS hT
  apply Set.Subset.antisymm
  · rintro x ⟨hxS, hxClosed⟩
    have hxRange : x ∈ Set.range X.pointMap := by
      rw [X.pointMap_range]
      exact hxClosed
    obtain ⟨p, rfl⟩ := hxRange
    exact ⟨(Set.ext_iff.mp hpoints p).mp hxS, hxClosed⟩
  · rintro x ⟨hxT, hxClosed⟩
    have hxRange : x ∈ Set.range X.pointMap := by
      rw [X.pointMap_range]
      exact hxClosed
    obtain ⟨p, rfl⟩ := hxRange
    exact ⟨(Set.ext_iff.mp hpoints p).mpr hxT, hxClosed⟩

private theorem mem_range_points_iff {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : GroupActions.Variety K} (f : X.toOver ⟶ Y.toOver) (p : Y.points) :
    Y.pointMap p ∈ Set.range f.left ↔ p ∈ Set.range (Variety.mapPoints f) := by
  change p ∈ Y.pointMap ⁻¹' Set.range (f.left : X.scheme → Y.scheme) ↔ _
  exact (Set.ext_iff.mp (Variety.range_mapPoints f) p).symm

/-- An opposite Schubert support is the union of the cells indexed above it
in Bruhat order, as subsets of the entire flag scheme. -/
theorem oppositeSchubert_range_cells {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) (w : G.weylGroup) :
    Set.range (oppositeSchubertInclusion G w).left =
      ⋃ v : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase w v),
        Set.range (oppositeSchubertCellInclusion G v).left := by
  classical
  let : Finite G.weylGroup := weylGroup_finite G.rootBase
  refine constructible_points_eq (flagVariety G)
    (Variety.isConstructible_range (oppositeSchubertInclusion G w))
    (IsConstructible.iUnion fun v => IsConstructible.iUnion fun _ =>
      Variety.isConstructible_range (oppositeSchubertCellInclusion G v)) ?_
  ext p
  change (flagVariety G).pointMap p ∈ Set.range (oppositeSchubertInclusion G w).left ↔ _
  rw [mem_range_points_iff (oppositeSchubertInclusion G w) p,
    oppositeSchubert_points_cells G w]
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨v, hv, hp⟩
    exact ⟨v, hv, (mem_range_points_iff (oppositeSchubertCellInclusion G v) p).mpr hp⟩
  · rintro ⟨v, hv, hp⟩
    exact ⟨v, hv, (mem_range_points_iff (oppositeSchubertCellInclusion G v) p).mp hp⟩

/-- Bruhat order gives reverse inclusion of opposite Schubert supports. -/
theorem oppositeSchubert_range_mono {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) {v w : G.weylGroup}
    (hvw : WeylBruhatLE G.rootBase v w) :
    Set.range (oppositeSchubertInclusion G w).left ⊆
      Set.range (oppositeSchubertInclusion G v).left := by
  rw [oppositeSchubert_range_cells G w, oppositeSchubert_range_cells G v]
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨z, hwz, hxz⟩ := hx
  exact ⟨z, hvw.trans hwz, hxz⟩

/-- An intersection of two opposite Schubert supports is the union of the
opposite Schubert supports indexed by their common Bruhat upper bounds. -/
theorem oppositeSchubert_range_inter {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) (a b : G.weylGroup) :
    Set.range (oppositeSchubertInclusion G a).left ∩
        Set.range (oppositeSchubertInclusion G b).left =
      ⋃ v : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase a v),
        ⋃ (_ : WeylBruhatLE G.rootBase b v),
          Set.range (oppositeSchubertInclusion G v).left := by
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    rw [oppositeSchubert_range_cells G a] at ha
    rw [oppositeSchubert_range_cells G b] at hb
    simp only [Set.mem_iUnion] at ha hb ⊢
    obtain ⟨v, hav, hxv⟩ := ha
    obtain ⟨w, hbw, hxw⟩ := hb
    have hvw := oppositeSchubertCells_disjoint G hxv hxw
    subst w
    refine ⟨v, hav, hbw, ?_⟩
    rw [oppositeSchubertInclusion_range G v]
    exact subset_closure hxv
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hav, hbv, hxv⟩ := hx
    exact ⟨oppositeSchubert_range_mono G hav hxv,
      oppositeSchubert_range_mono G hbv hxv⟩

/-- Inclusion of opposite Schubert supports detects their reverse Bruhat order. -/
theorem oppositeSchubert_range_subset_iff {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) (v w : G.weylGroup) :
    (Set.range (oppositeSchubertInclusion G w).left ⊆
      Set.range (oppositeSchubertInclusion G v).left) ↔
      WeylBruhatLE G.rootBase v w := by
  constructor
  · intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty (oppositeSchubertCell G w).scheme)
    have hxw : (oppositeSchubertCellInclusion G w).left x ∈
        Set.range (oppositeSchubertCellInclusion G w).left := ⟨x, rfl⟩
    have hw : (oppositeSchubertCellInclusion G w).left x ∈
        Set.range (oppositeSchubertInclusion G w).left := by
      rw [oppositeSchubertInclusion_range G w]
      exact subset_closure hxw
    have hv := h hw
    rw [oppositeSchubert_range_cells G v] at hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨z, hvz, hxz⟩ := hv
    have hzw := oppositeSchubertCells_disjoint G hxz hxw
    simpa only [hzw] using hvz
  · exact oppositeSchubert_range_mono G

end SchubertGeometry
