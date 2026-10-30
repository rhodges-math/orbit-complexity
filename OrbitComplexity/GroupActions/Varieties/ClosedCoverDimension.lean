import Mathlib.Topology.KrullDimension

/-! # Dimension bounds from finite closed covers

The largest member of an irreducible closed chain lies in one member of a finite closed
cover. Restricting the chain gives a dimension bound from that member.

## Main results

* `GroupActions.topologicalKrullDim_le_closed_cover`: finite closed covers bound dimension.
-/

open Set Topology TopologicalSpace Order

namespace GroupActions

private theorem preimage_irreducible {X : Type*} [TopologicalSpace X]
    (S : Set X) (Z : IrreducibleCloseds X) (hZ : (Z : Set X) ⊆ S) :
    IsIrreducible ((Subtype.val : S → X) ⁻¹' Z) := by
  have : IrreducibleSpace (Z : Set X) := Subtype.irreducibleSpace Z.isIrreducible
  let e := (IsEmbedding.subtypeVal (p := (· ∈ S))).homeomorphOfSubsetRange
    (show (Z : Set X) ⊆ range (Subtype.val : S → X) by simpa using hZ)
  have : IrreducibleSpace ((Subtype.val : S → X) ⁻¹' Z) :=
    e.irreducibleSpace_iff.mpr inferInstance
  exact isIrreducible_iff_irreducibleSpace.mpr inferInstance

/-- Dimensions of members of a finite closed cover bound the dimension of the space. -/
theorem topologicalKrullDim_le_closed_cover {X ι : Type*} [TopologicalSpace X]
    [Finite ι] (S : ι → Set X) (hS : ∀ i, IsClosed (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i) (d : WithBot ℕ∞)
    (hd : ∀ i, topologicalKrullDim (S i) ≤ d) : topologicalKrullDim X ≤ d := by
  classical
  let := Fintype.ofFinite ι
  refine iSup_le fun p ↦ ?_
  let T : Finset (Set X) := Finset.univ.image S
  have hT : ∀ Z ∈ T, IsClosed Z := by
    intro Z hZ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
    exact hS i
  have hlast : (p.last : Set X) ⊆ ⋃₀ (T : Set (Set X)) := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact mem_sUnion.mpr ⟨S i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  obtain ⟨Z, hZT, hpZ⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp p.last.isIrreducible T hT hlast
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZT
  have hpS (j : Fin (p.length + 1)) : (p j : Set X) ⊆ S i := by
    intro x hx
    exact hpZ (p.monotone (Fin.le_last j) hx)
  let q : LTSeries (IrreducibleCloseds (S i)) :=
    ⟨p.length, fun j ↦ ⟨(Subtype.val : S i → X) ⁻¹' p j,
      preimage_irreducible (S i) (p j) (hpS j),
      (p j).isClosed.preimage continuous_subtype_val⟩, fun j ↦ by
        change ((Subtype.val : S i → X) ⁻¹' (p j.castSucc : Set X)) ⊂
          (Subtype.val : S i → X) ⁻¹' (p j.succ : Set X)
        have hle : p j.castSucc ≤ p j.succ := (p.step j).le
        refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
        · exact preimage_mono (show (p j.castSucc : Set X) ⊆ p j.succ from hle)
        · intro h
          have hlt : p j.castSucc < p j.succ := p.step j
          apply not_le_of_gt hlt
          intro x hx
          exact h (show (⟨x, hpS _ hx⟩ : S i) ∈
            (Subtype.val : S i → X) ⁻¹' p j.succ from hx)⟩
  exact q.length_le_krullDim.trans (hd i)

end GroupActions
