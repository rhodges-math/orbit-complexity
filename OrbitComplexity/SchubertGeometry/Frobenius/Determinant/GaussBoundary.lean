import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussOrbit
import OrbitComplexity.SchubertGeometry.Cells.OppositeClosure
import OrbitComplexity.GroupActions.Varieties.OpenPoints
import Batteries.Tactic.Lint

/-!
# The boundary of the Gauss cell

The complement of the identity Gauss chart is the union of the opposite Schubert
varieties indexed by simple reflections. Rational-point incidence is transferred
to the underlying scheme through constructibility.
-/

open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups Topology

namespace SchubertGeometry.DeterminantSection

universe u

private theorem constructible_eq_of_points {K : Type u} [Field K] [IsAlgClosed K]
    (X : Variety K) {S T : Set X.scheme} (hS : IsConstructible S)
    (hT : IsConstructible T) (h : X.pointMap ⁻¹' S = X.pointMap ⁻¹' T) : S = T := by
  let : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  apply GroupActions.constructible_eq hS hT
  ext p
  by_cases hp : p ∈ closedPoints X.scheme
  · have hp' : p ∈ Set.range X.pointMap := by
      rw [X.pointMap_range]
      exact hp
    obtain ⟨x, rfl⟩ := hp'
    exact and_congr (Set.ext_iff.mp h x) Iff.rfl
  · simp only [Set.mem_inter_iff, hp, and_false]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

private theorem simple_word_length (i : G.rootBase.support) :
    rootInversionCount G.rootBase (simpleWeylWord G.rootBase [i]) = 1 := by
  simpa only [List.length_singleton] using
    RootInversionCount.simpleWeylWord_eq_length G.rootBase [i] (by simp)

private theorem nontrivial_simple_below (w : G.weylGroup) (hw : w ≠ 1) :
    ∃ i : G.rootBase.support,
      WeylBruhatLE G.rootBase (simpleWeylWord G.rootBase [i]) w := by
  obtain ⟨word, hprod, hlen⟩ :=
    InversionLength.exists_of_inversionCount_length G.rootBase w
  cases word with
  | nil => exact (hw (by simpa only [simpleWeylWord] using hprod.symm)).elim
  | cons i word =>
    refine ⟨i, i :: word, [i], ?_, hprod, rfl, ?_, ?_⟩
    · exact List.singleton_sublist.mpr List.mem_cons_self
    · rw [hprod, ← hlen]
    · simpa only [List.length_singleton] using simple_word_length G i

private theorem opposite_boundary_points :
    (Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G 1)))ᶜ =
      ⋃ i : G.rootBase.support,
        Set.range (Variety.mapPoints
          (oppositeSchubertInclusion G (simpleWeylWord G.rootBase [i]))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := oppositeSchubertOrbits_cover G x
    have hwne : w ≠ 1 := by
      intro h
      apply hx
      rw [oppositeSchubertCell_points_range, ← h]
      exact hw
    obtain ⟨i, hi⟩ := nontrivial_simple_below G w hwne
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [oppositeSchubert_points_cells]
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr
      ⟨hi, (Set.ext_iff.mp (oppositeSchubertCell_points_range G w) x).mpr hw⟩⟩
  · intro hx hbig
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [oppositeSchubert_points_cells] at hi
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hi
    obtain ⟨hle, hxw⟩ := Set.mem_iUnion.mp hw
    have heq : w = 1 := oppositeSchubertOrbits_disjoint G
      ((Set.ext_iff.mp (oppositeSchubertCell_points_range G w) x).mp hxw)
      ((Set.ext_iff.mp (oppositeSchubertCell_points_range G 1) x).mp hbig)
    have hbound := hle.length_le
    rw [heq, rootInversionCount_one, simple_word_length] at hbound
    omega

/-- The boundary of the identity Gauss chart is the union of the simple
opposite Schubert varieties. -/
theorem gauss_boundary_schubert :
    (Set.range (flagChartMorphism G 1).left)ᶜ =
      ⋃ i : G.rootBase.support,
        Set.range (oppositeSchubertInclusion G (simpleWeylWord G.rootBase [i])).left := by
  apply constructible_eq_of_points (flagVariety G)
    (Variety.isConstructible_range (flagChartMorphism G 1)).compl
    (IsConstructible.iUnion (fun i => Variety.isConstructible_range
      (oppositeSchubertInclusion G (simpleWeylWord G.rootBase [i]))))
  rw [Set.preimage_compl, gauss_oppositeCell_range, ← Variety.range_mapPoints]
  simp only [Set.preimage_iUnion]
  refine (opposite_boundary_points G).trans ?_
  exact Set.iUnion_congr fun i => Variety.range_mapPoints
    (X := oppositeSchubertVariety G (simpleWeylWord G.rootBase [i]))
    (Y := flagVariety G)
    (oppositeSchubertInclusion G (simpleWeylWord G.rootBase [i]))

end SchubertGeometry.DeterminantSection
