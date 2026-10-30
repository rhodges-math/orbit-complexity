import OrbitComplexity.SchubertGeometry.Cells.CellAffine
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Schubert cells as unipotent images and affine spaces

The flag image of the inversion subgroup is the Schubert cell. Its polynomial coordinate
chart identifies it with affine space of the Weyl element's Coxeter length.
-/

namespace SchubertOrbits
noncomputable section
open CategoryTheory GroupActions ReductiveGroups SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A Schubert cell is the inversion subgroup's flag image and affine space of its Weyl length. -/
theorem schubert_cell_affine (w : G.weylGroup) :
  schubertUnipotentPoints G w =
      G.unipotentPoints ⊓ G.oppositeUnipotentPoints.map
        (MulAut.conj (G.weylPoint w)).toMonoidHom ∧
  Set.range ((schubertCellInclusion G w).left : (schubertCell G w).scheme →
      (flagVariety G).scheme) =
    Set.range ((schubertRootMorphism G w).left : (schubertUnipotent G w).scheme →
      (flagVariety G).scheme) ∧
  Set.range (Variety.mapPoints (schubertCellInclusion G w)) =
    Set.range (fun u : schubertUnipotentPoints G w =>
      flagVarietyPointsEquiv G (flagProjection G ((u : G.points) * G.weylPoint w))) ∧
  (∃ e : (schubertUnipotent G w).toOver ≅ (schubertCell G w).toOver,
    e.hom ≫ schubertCellInclusion G w = schubertRootMorphism G w) ∧
  Nonempty ((schubertCell G w).toOver ≅
    (affineVariety K (MvPolynomial (Fin ((weylCoxeterSystem G.rootBase).length w)) K)).toOver) := by
  exact ⟨G.inversionPoints_eq_inter w, schubertCell_scheme_unipotent G w,
    schubertCell_points_unipotent G w,
    ⟨schubertCellIso G w, schubertCellIso_hom_comp G w⟩, ⟨schubertCellAffineIso G w⟩⟩

/-- Over the complex numbers, a Schubert cell is its inversion-group image and affine space. -/
theorem schubert_cell_affine_complex (G : ReductiveGroupData ℂ) (w : G.weylGroup) :
  schubertUnipotentPoints G w =
      G.unipotentPoints ⊓ G.oppositeUnipotentPoints.map
        (MulAut.conj (G.weylPoint w)).toMonoidHom ∧
  Set.range ((schubertCellInclusion G w).left : (schubertCell G w).scheme →
      (flagVariety G).scheme) =
    Set.range ((schubertRootMorphism G w).left : (schubertUnipotent G w).scheme →
      (flagVariety G).scheme) ∧
  Set.range (Variety.mapPoints (schubertCellInclusion G w)) =
    Set.range (fun u : schubertUnipotentPoints G w =>
      flagVarietyPointsEquiv G (flagProjection G ((u : G.points) * G.weylPoint w))) ∧
  (∃ e : (schubertUnipotent G w).toOver ≅ (schubertCell G w).toOver,
    e.hom ≫ schubertCellInclusion G w = schubertRootMorphism G w) ∧
  Nonempty ((schubertCell G w).toOver ≅
    (affineVariety ℂ (MvPolynomial (Fin ((weylCoxeterSystem G.rootBase).length w)) ℂ)).toOver) :=
  schubert_cell_affine G w

end
end SchubertOrbits
