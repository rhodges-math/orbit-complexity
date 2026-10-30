import OrbitComplexity.SchubertGeometry.Levi.Schubert
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.GroupActions.Varieties.ImmersionDimension
/-! # Codimensions of lower Schubert cells

The lower-cell immersion preserves the dimension of its image closure.
Its codimension is the difference of Weyl lengths, and orbit codimensions
increase by that amount under the lower-cell inclusion.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions Topology TopologicalSpace ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
/-- The closure of a lower cell in a Schubert variety has the cell dimension. -/
theorem schubertLowerCell_subsetDim (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) :
    (schubertVariety G w).subsetDim
        (Set.range (Variety.mapPoints (schubertCellOfLE G u w huw))) =
      (schubertCell G u).dim := by
  unfold Variety.subsetDim
  rw [Variety.pointClosure_range]
  have h := Variety.dim_closure_image_immersion (schubertCellOfLE G u w huw)
    Set.univ isOpen_univ.isLocallyClosed
    (IrreducibleSpace.isIrreducible_univ (schubertCell G u).scheme)
  calc
    _ = topologicalKrullDim (closure
        ((schubertCellOfLE G u w huw).left '' (Set.univ : Set (schubertCell G u).scheme))) := by
      rw [Set.image_univ]
    _ = topologicalKrullDim (closure (Set.univ : Set (schubertCell G u).scheme)) := h
    _ = (schubertCell G u).dim := by
      rw [closure_univ]
      exact (Homeomorph.Set.univ (schubertCell G u).scheme).isHomeomorph.topologicalKrullDim_eq

/-- The codimension of the closure of a lower cell inside its Schubert variety. -/
def schubertLowerCellCodim (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) : ℤ :=
  ((schubertVariety G w).natDim : ℤ) -
    (((schubertVariety G w).subsetDim
      (Set.range (Variety.mapPoints (schubertCellOfLE G u w huw)))).unbotD 0).toNat

private theorem cell_natDim (u : G.weylGroup) :
    (schubertCell G u).natDim = (weylCoxeterSystem G.rootBase).length u := by
  have h := (schubertCell G u).natDim_cast
  rw [schubertCell_dim, ← weylCoxeterSystem_length] at h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp h)
private theorem variety_natDim (u : G.weylGroup) :
    (schubertVariety G u).natDim = (weylCoxeterSystem G.rootBase).length u := by
  have h := (schubertVariety G u).natDim_cast
  rw [schubertVariety_dim, ← weylCoxeterSystem_length] at h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp h)
/-- A lower Schubert cell has codimension equal to the difference of Weyl lengths. -/
theorem schubertLowerCellCodim_eq (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) :
    schubertLowerCellCodim G u w huw =
      ((weylCoxeterSystem G.rootBase).length w : ℤ) -
        (weylCoxeterSystem G.rootBase).length u := by
  unfold schubertLowerCellCodim
  rw [schubertLowerCell_subsetDim]
  change ((schubertVariety G w).natDim : ℤ) - (schubertCell G u).natDim = _
  rw [variety_natDim, cell_natDim]
/-- Lower-cell inclusion adds the cell codimension to each Levi--Borel orbit codimension. -/
theorem schubertLowerOrbitCodim (I : Set G.rootBase.support) (u w : G.weylGroup)
    (huw : WeylBruhatLE G.rootBase u w) (q : (schubertCell G u).points) :
    orbitCodim (leviBorelVariety G I) (schubertVariety G w)
        (Variety.mapPoints (schubertCellOfLE G u w huw) q) =
      schubertLowerCellCodim G u w huw +
        orbitCodim (leviBorelVariety G I) (schubertCell G u) q := by
  rw [schubertLowerCellCodim_eq]
  unfold orbitCodim
  rw [schubertCellOfLE_orbitNatDim, variety_natDim, cell_natDim]
  omega
end SchubertGeometry
