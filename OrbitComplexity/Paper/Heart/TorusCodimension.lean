import OrbitComplexity.Paper.Heart.OrbitTransport
import OrbitComplexity.SchubertGeometry.Cells.TorusComplexity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Torus codimensions in the heart

The dimension of the minimal cell is the dimension of the heart. Its torus
complexity bounds every heart orbit codimension and bounds that of its closure.
-/

open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
noncomputable section
namespace SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem heart_natDim (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    (heart G I w).natDim = (weylCoxeterSystem G.rootBase).length
      (leftParabolicRepresentative G.rootBase I w) := by
  have : Nonempty (heart G I w).scheme := ⟨(heart G I w).pointMap h⟩
  have hd := (Variety.dim_eq_of_iso (heart G I w) (heartMinimalIso G I w)).trans
    (schubertCell_dim G (leftParabolicRepresentative G.rootBase I w))
  have hc := (heart G I w).natDim_cast.trans hd
  rw [weylCoxeterSystem_length]
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hc)

/-- A heart torus orbit has length-minus-orbit codimension, bounded below by the
minimal cell complexity and then by the Schubert closure complexity. -/
theorem heart_torus_codimension (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    ((weylCoxeterSystem G.rootBase).length
        (leftParabolicRepresentative G.rootBase I w) : ℤ) -
      orbitNatDim (torusVariety G) (heart G I w) h =
        orbitCodim (torusVariety G) (heart G I w) h ∧
    (torusComplexity G
      (schubertCell G (leftParabolicRepresentative G.rootBase I w)) : ℤ) ≤
        orbitCodim (torusVariety G) (heart G I w) h ∧
    torusComplexity G (schubertVariety G (leftParabolicRepresentative G.rootBase I w)) ≤
      torusComplexity G (schubertCell G (leftParabolicRepresentative G.rootBase I w)) := by
  refine ⟨?_, ?_, (torus_cell_complexity G _).symm.le⟩
  · unfold orbitCodim
    rw [heart_natDim G I w h]
  · rw [heart_orbitCodim G I w h]
    exact torusComplexity_le G _ (Variety.mapPoints (heartMinimalIso G I w).hom h)

/-- The complete heart torus-orbit codimension comparison over the complex numbers. -/
theorem heart_torus_codimension_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) (h : (heart G I w).points) :
    ((weylCoxeterSystem G.rootBase).length
        (leftParabolicRepresentative G.rootBase I w) : ℤ) -
      orbitNatDim (torusVariety G) (heart G I w) h =
        orbitCodim (torusVariety G) (heart G I w) h ∧
    (torusComplexity G
      (schubertCell G (leftParabolicRepresentative G.rootBase I w)) : ℤ) ≤
        orbitCodim (torusVariety G) (heart G I w) h ∧
    torusComplexity G (schubertVariety G (leftParabolicRepresentative G.rootBase I w)) ≤
      torusComplexity G (schubertCell G (leftParabolicRepresentative G.rootBase I w)) :=
  heart_torus_codimension G I w h

end SchubertOrbits
