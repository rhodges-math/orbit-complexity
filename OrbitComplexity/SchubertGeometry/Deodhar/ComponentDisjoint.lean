import OrbitComplexity.SchubertGeometry.Deodhar.Components
import OrbitComplexity.BruhatIntervals.Words.PrefixInjective
import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition

/-! # Disjoint intrinsic Deodhar components

Every prefix lies in a unique opposite Schubert cell. A flag in two full components
therefore gives equal prefix products, which determine the entire subexpression.
-/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem prefix_eq_of_mem (a b : Subexpression word)
    {x : (wordCell G word word.length).scheme}
    (ha : x ∈ Set.range (deodharPrefixInclusion G a hred word.length).left)
    (hb : x ∈ Set.range (deodharPrefixInclusion G b hred word.length).left) : a = b := by
  apply Subexpression.eq_of_prefixProd (weylCoxeterSystem G.rootBase) a b
  intro k hk
  rw [deodharPrefixInclusion_range] at ha hb
  have hA := (Set.mem_iInter.mp ha) ⟨k, Nat.lt_succ_iff.mpr hk⟩
  have hB := (Set.mem_iInter.mp hb) ⟨k, Nat.lt_succ_iff.mpr hk⟩
  exact oppositeSchubertCells_disjoint G hA hB

/-- Intrinsic Deodhar components sharing a flag scheme point have the same subexpression. -/
theorem deodharInclusion_disjoint (a b : Subexpression word)
    {x : (flagVariety G).scheme}
    (ha : x ∈ Set.range (deodharInclusion G a hred).left)
    (hb : x ∈ Set.range (deodharInclusion G b hred).left) : a = b := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  let i := schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))
  have he : i.left ((deodharPrefixInclusion G a hred word.length).left p) =
      i.left ((deodharPrefixInclusion G b hred word.length).left q) := hp.trans hq.symm
  have hpq := i.left.isEmbedding.injective he
  exact prefix_eq_of_mem G hred a b ⟨p, rfl⟩ ⟨q, hpq.symm⟩

end
end SchubertGeometry
