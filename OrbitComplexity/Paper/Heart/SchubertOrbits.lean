import OrbitComplexity.SchubertGeometry.Cells.OrbitDecomposition
import OrbitComplexity.SchubertGeometry.Cells.OrbitDecompositionDimension
import OrbitComplexity.SchubertGeometry.Parabolics.LeftOrder
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Schubert cells and Levi--Borel orbit quotients

The Bruhat partition of a Schubert variety partitions its Levi--Borel orbits.
The lower-cell inclusions determine their codimensions, and minimum left
parabolic representatives preserve the Bruhat comparison of cell indices.
-/

noncomputable section
namespace SchubertOrbits
open CategoryTheory GroupActions ReductiveGroups SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The lower-cell partition, Levi--Borel orbit partition, codimensions and left representatives. -/
theorem schubert_orbit_decomposition (I : Set G.rootBase.support) (w : G.weylGroup) :
  (∀ p : (schubertVariety G w).scheme,
    ∃! u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      p ∈ Set.range (schubertCellOfLE G u.val w u.property).left) ∧
  (∃ e : MulAction.orbitRel.Quotient (leviBorelVariety G I).points
      (schubertVariety G w).points ≃
      Σ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points
          (schubertCell G u.val).points,
    ∀ (u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w})
      (q : (schubertCell G u.val).points),
      e.symm ⟨u, ⟦q⟧⟩ = ⟦Variety.mapPoints (schubertCellOfLE G u.val w u.property) q⟧) ∧
  (∀ (u : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w),
    ((schubertVariety G w).natDim : ℤ) -
      (((schubertVariety G w).subsetDim
        (Set.range (Variety.mapPoints (schubertCellOfLE G u w huw)))).unbotD 0).toNat =
      ((weylCoxeterSystem G.rootBase).length w : ℤ) -
        (weylCoxeterSystem G.rootBase).length u) ∧
  (∀ (u : G.weylGroup), WeylBruhatLE G.rootBase u w →
    WeylBruhatLE G.rootBase (leftParabolicRepresentative G.rootBase I u)
      (leftParabolicRepresentative G.rootBase I w)) := by
  refine ⟨schubertLowerCells_partition G w, ?_, ?_, ?_⟩
  · exact ⟨schubertOrbitDecomposition G I w,
      schubertOrbitDecomposition_symm_mk G I w⟩
  · exact fun u huw => schubertLowerCellCodim_eq G u w huw
  · exact fun u huw => leftParabolicRepresentative_mono G.rootBase I u w huw

/-- The Schubert-cell and Levi--Borel orbit decomposition over the complex numbers. -/
theorem schubert_orbit_decomposition_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
  (∀ p : (schubertVariety G w).scheme,
    ∃! u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      p ∈ Set.range (schubertCellOfLE G u.val w u.property).left) ∧
  (∃ e : MulAction.orbitRel.Quotient (leviBorelVariety G I).points
      (schubertVariety G w).points ≃
      Σ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points
          (schubertCell G u.val).points,
    ∀ (u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w})
      (q : (schubertCell G u.val).points),
      e.symm ⟨u, ⟦q⟧⟩ = ⟦Variety.mapPoints (schubertCellOfLE G u.val w u.property) q⟧) ∧
  (∀ (u : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w),
    ((schubertVariety G w).natDim : ℤ) -
      (((schubertVariety G w).subsetDim
        (Set.range (Variety.mapPoints (schubertCellOfLE G u w huw)))).unbotD 0).toNat =
      ((weylCoxeterSystem G.rootBase).length w : ℤ) -
        (weylCoxeterSystem G.rootBase).length u) ∧
  (∀ (u : G.weylGroup), WeylBruhatLE G.rootBase u w →
    WeylBruhatLE G.rootBase (leftParabolicRepresentative G.rootBase I u)
      (leftParabolicRepresentative G.rootBase I w)) :=
  schubert_orbit_decomposition G I w

end SchubertOrbits
