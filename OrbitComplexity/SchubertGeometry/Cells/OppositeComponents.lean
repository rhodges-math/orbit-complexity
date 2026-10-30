import OrbitComplexity.SchubertGeometry.Cells.OppositeSupports
import OrbitComplexity.BruhatIntervals.Intervals.TwoCovers
import Batteries.Tactic.Lint

/-! # Components of intersections of opposite Schubert varieties

The common top of two distinct Bruhat covers defines an irreducible component
of their opposite Schubert intersection. Finite closed covers reduce this
assertion to the minimality of the common Bruhat upper bound.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology

namespace SchubertGeometry

universe u v

private theorem irreducible_subset_finite_cover {X : Type u}
    [TopologicalSpace X] {ι : Type v} [Finite ι] (Z : Set X)
    (C : ι → Set X) (hZ : IsIrreducible Z) (hC : ∀ i, IsClosed (C i))
    (hcover : Z ⊆ ⋃ i, C i) : ∃ i, Z ⊆ C i := by
  classical
  let := Fintype.ofFinite ι
  have hcover' : Z ⊆ ⋃₀ (↑(Finset.univ.image C) : Set (Set X)) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.sUnion_range] using hcover
  obtain ⟨D, hD, hZD⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ
    (Finset.univ.image C) (by
      intro D hD
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
      exact hC i) hcover'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
  exact ⟨i, hZD⟩

private theorem opposite_component_of_covers {K : Type u} [Field K]
    [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
    (a b w : G.weylGroup) (hab : a ≠ b) :
    let : PartialOrder G.weylGroup := (weylCoxeterSystem G.rootBase).bruhatPartialOrder
    a ⋖ w → b ⋖ w →
      Maximal (fun Z : Set (flagVariety G).scheme => IsIrreducible Z ∧
        Z ⊆ Set.range (oppositeSchubertInclusion G a).left ∩
          Set.range (oppositeSchubertInclusion G b).left)
        (Set.range (oppositeSchubertInclusion G w).left) := by
  classical
  let : PartialOrder G.weylGroup := (weylCoxeterSystem G.rootBase).bruhatPartialOrder
  dsimp only
  intro ha hb
  let : Finite G.weylGroup := weylGroup_finite G.rootBase
  have hirred : IsIrreducible (Set.range (oppositeSchubertInclusion G w).left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (oppositeSchubertVariety G w).scheme).image
        (oppositeSchubertInclusion G w).left
        (oppositeSchubertInclusion G w).left.continuous.continuousOn
  have hsubset : Set.range (oppositeSchubertInclusion G w).left ⊆
      Set.range (oppositeSchubertInclusion G a).left ∩
        Set.range (oppositeSchubertInclusion G b).left := by
    intro x hx
    exact ⟨oppositeSchubert_range_mono G
      ((weyl_bruhat_iff G.rootBase a w).mpr ha.le) hx,
      oppositeSchubert_range_mono G
        ((weyl_bruhat_iff G.rootBase b w).mpr hb.le) hx⟩
  refine ⟨⟨hirred, hsubset⟩, ?_⟩
  intro Z hZ hwZ
  have hcover : Z ⊆ ⋃ v : {v : G.weylGroup //
      WeylBruhatLE G.rootBase a v ∧ WeylBruhatLE G.rootBase b v},
      Set.range (oppositeSchubertInclusion G v.val).left := by
    intro x hx
    have hx' := hZ.2 hx
    rw [oppositeSchubert_range_inter G a b] at hx'
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨v, hav, hbv, hxv⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨⟨v, hav, hbv⟩, hxv⟩
  obtain ⟨v, hZv⟩ := irreducible_subset_finite_cover Z
    (fun v : {v : G.weylGroup //
      WeylBruhatLE G.rootBase a v ∧ WeylBruhatLE G.rootBase b v} =>
        Set.range (oppositeSchubertInclusion G v.val).left)
    hZ.1 (fun v => (oppositeSchubertInclusion_range G v.val).symm ▸ isClosed_closure)
    hcover
  have hvw : WeylBruhatLE G.rootBase v.val w :=
    (oppositeSchubert_range_subset_iff G v.val w).mp (hwZ.trans hZv)
  have hv : v.val = w := BruhatIntervals.bruhat_cover_minimal_upper
    (weylCoxeterSystem G.rootBase) a b w v.val hab ha hb
    ((weyl_bruhat_iff G.rootBase a v.val).mp v.property.1)
    ((weyl_bruhat_iff G.rootBase b v.val).mp v.property.2)
    ((weyl_bruhat_iff G.rootBase v.val w).mp hvw)
  exact hv ▸ hZv

/-- Every opposite Schubert variety of codimension at least two is an
irreducible component of an intersection of two opposite Schubert varieties
of smaller codimension. -/
theorem exists_oppositeSchubert_components {K : Type u} [Field K]
    [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K) (w : G.weylGroup)
    (hw : 2 ≤ (weylCoxeterSystem G.rootBase).length w) :
    ∃ a b : G.weylGroup, a ≠ b ∧
      (weylCoxeterSystem G.rootBase).length a <
        (weylCoxeterSystem G.rootBase).length w ∧
      (weylCoxeterSystem G.rootBase).length b <
        (weylCoxeterSystem G.rootBase).length w ∧
      Maximal (fun Z : Set (flagVariety G).scheme => IsIrreducible Z ∧
        Z ⊆ Set.range (oppositeSchubertInclusion G a).left ∩
          Set.range (oppositeSchubertInclusion G b).left)
        (Set.range (oppositeSchubertInclusion G w).left) := by
  let : PartialOrder G.weylGroup := (weylCoxeterSystem G.rootBase).bruhatPartialOrder
  have hlength : (weylCoxeterSystem G.rootBase).length (1 : G.weylGroup) + 2 ≤
      (weylCoxeterSystem G.rootBase).length w := by
    simpa only [(weylCoxeterSystem G.rootBase).length_one, zero_add] using hw
  obtain ⟨a, b, hab, ha, hb, _, _⟩ := BruhatIntervals.exists_two_bruhat_covBy
    (weylCoxeterSystem G.rootBase) 1 w
    ((weylCoxeterSystem G.rootBase).one_bruhatLE w) hlength
  have hla := (BruhatIntervals.bruhat_covBy_iff (weylCoxeterSystem G.rootBase) a w).mp ha
  have hlb := (BruhatIntervals.bruhat_covBy_iff (weylCoxeterSystem G.rootBase) b w).mp hb
  exact ⟨a, b, hab, by omega, by omega,
    opposite_component_of_covers G a b w hab ha hb⟩

end SchubertGeometry
