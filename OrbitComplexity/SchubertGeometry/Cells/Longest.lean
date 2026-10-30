import OrbitComplexity.SchubertGeometry.Cells.Decomposition
import OrbitComplexity.SchubertGeometry.Levi.Schubert
import OrbitComplexity.SchubertGeometry.Parabolics.Order

/-! # The longest Schubert variety and the flag variety

Every Weyl element lies below the longest element. The scheme Bruhat decomposition
then identifies the longest cell's closure with the full flag variety.
-/

namespace SchubertGeometry
noncomputable section
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem weyl_le_longest (w : G.weylGroup) :
    WeylBruhatLE G.rootBase w G.longestElement := by
  let cs := weylCoxeterSystem G.rootBase
  have hd (i : G.rootBase.support) : cs.IsLeftDescent G.longestElement i := by
    by_contra hn
    have hinc := cs.not_isLeftDescent_iff.mp hn
    change (weylCoxeterSystem G.rootBase).length (cs.simple i * G.longestElement) =
      (weylCoxeterSystem G.rootBase).length G.longestElement + 1 at hinc
    rw [weylCoxeterSystem_length, weylCoxeterSystem_length] at hinc
    have hbound : rootInversionCount G.rootBase (cs.simple i * G.longestElement) ≤
        rootInversionCount G.rootBase G.longestElement :=
      rootInversionCount_le_longest G.rootBase _
    omega
  have hword (word : List G.rootBase.support) :
      cs.BruhatLE (cs.wordProd word) G.longestElement := by
    induction word with
    | nil => exact cs.one_bruhatLE _
    | cons i word ih =>
      have hi := cs.isRightDescent_inv_iff.mpr (hd i)
      have hs := (ih.inv.mul_simple_of_isRightDescent i hi).inv
      simpa only [mul_inv_rev, cs.inv_simple, inv_inv, cs.wordProd_cons] using hs
  obtain ⟨word, rfl⟩ := cs.wordProd_surjective w
  exact (weyl_bruhat_iff G.rootBase _ _).mpr (hword word)

/-- The longest Schubert cell has the whole flag variety as its closed support. -/
theorem schubertSupport_longest : schubertSupport G G.longestElement = ⊤ := by
  apply SetLike.coe_injective
  apply Set.eq_univ_iff_forall.mpr
  intro q
  change q ∈ closure (Set.range (schubertCellInclusion G G.longestElement).left)
  rw [← schubertInclusion_range]
  obtain ⟨v, p, hp⟩ := schubertCells_cover G q
  let hv := weyl_le_longest G v
  refine ⟨(schubertCellOfLE G v G.longestElement hv).left p, ?_⟩
  exact (congrArg (fun f => f.left p)
    (schubertCellOfLE_comp G v G.longestElement hv)).trans hp

/-- The longest Schubert cell is dense in the flag variety on all scheme points. -/
theorem longestCell_dense : DenseRange (schubertCellInclusion G G.longestElement).left := by
  rw [denseRange_iff_closure_range]
  exact congrArg (fun Z : TopologicalSpace.Closeds (flagVariety G).scheme =>
    (Z : Set (flagVariety G).scheme)) (schubertSupport_longest G)

private instance longestInclusion_isIso :
    IsIso (schubertInclusion G G.longestElement).left := by
  have hr : Set.range (schubertInclusion G G.longestElement).left = Set.univ := by
    rw [schubertInclusion_range]
    exact (denseRange_iff_closure_range).mp (longestCell_dense G)
  have : Surjective (schubertInclusion G G.longestElement).left :=
    ⟨Set.range_eq_univ.mp hr⟩
  have : IsReduced (flagVariety G).toOver.left := (flagVariety G).reduced
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The longest Schubert variety is isomorphic to the flag variety over the coefficient field. -/
def longestSchubertIso :
    (schubertVariety G G.longestElement).toOver ≅ (flagVariety G).toOver := by
  have : IsIso ((Over.forget _).map (schubertInclusion G G.longestElement)) := by
    change IsIso (schubertInclusion G G.longestElement).left
    infer_instance
  have : IsIso (schubertInclusion G G.longestElement) :=
    isIso_of_reflects_iso _ (Over.forget _)
  exact asIso (schubertInclusion G G.longestElement)

/-- The longest Schubert isomorphism is its inclusion in the flag variety. -/
theorem longestSchubertIso_hom :
    (longestSchubertIso G).hom = schubertInclusion G G.longestElement := rfl

end
end SchubertGeometry
