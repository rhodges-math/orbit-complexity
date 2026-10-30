import OrbitComplexity.Paper.Heart.OrbitCodimension
import OrbitComplexity.Paper.RichardsonComplexity

/-! # Torus complexity bounds for Levi--Borel cell orbits -/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
  Topology BruhatIntervals
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem cell_natDim (w : G.weylGroup) :
    (schubertCell G w).natDim = (weylCoxeterSystem G.rootBase).length w := by
  have he := (schubertCell G w).natDim_cast
  rw [schubertCell_dim, ← weylCoxeterSystem_length] at he
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp he)

/-- Torus complexity minus the parabolic length difference bounds cell orbit codimension. -/
private theorem levi_orbit_codimension_lower (I : Set G.rootBase.support) (w : G.weylGroup)
    (q : (schubertCell G w).points) (h : (heart G I w).points)
    (hq : Variety.mapPoints (heartCellInclusion G I w) h ∈
      MulAction.orbit (leviBorelVariety G I).points q) :
    (torusComplexity G
      (schubertVariety G (leftParabolicRepresentative G.rootBase I w)) : ℤ) -
      ((weylCoxeterSystem G.rootBase).length (longestParabolicElement G.rootBase I) -
        ((weylCoxeterSystem G.rootBase).length (leftParabolicFactor G.rootBase I w) : ℤ)) ≤
    orbitCodim (leviBorelVariety G I) (schubertCell G w) q := by
  rcases levi_orbit_codimension_chain G I w q h hq with
    ⟨_, _, _, _, _, _, _, _, _, hmain⟩
  rcases heart_torus_codimension G I w h with ⟨hdim, hcell, hclosure⟩
  have hclosure' : (torusComplexity G
      (schubertVariety G (leftParabolicRepresentative G.rootBase I w)) : ℤ) ≤
      torusComplexity G
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) := by
    exact_mod_cast hclosure
  unfold orbitCodim
  rw [cell_natDim]
  omega

/-- A Levi--Borel orbit has the cell and ambient Schubert codimension bounds. -/
theorem levi_orbit_codimension_bounds (I : Set G.rootBase.support) (u w : G.weylGroup)
    (huw : WeylBruhatLE G.rootBase u w) (q : (schubertCell G u).points)
    (h : (heart G I u).points)
    (hq : Variety.mapPoints (heartCellInclusion G I u) h ∈
      MulAction.orbit (leviBorelVariety G I).points q) :
    let cs := weylCoxeterSystem G.rootBase
    let d := leftParabolicRepresentative G.rootBase I u
    let n := longestParabolicElement G.rootBase I
    ((cs.length u : ℤ) - supportCard cs d - cs.length n ≤
      orbitCodim (leviBorelVariety G I) (schubertCell G u) q) ∧
    ((cs.length w : ℤ) - supportCard cs d - cs.length n ≤
      orbitCodim (leviBorelVariety G I) (schubertVariety G w)
        (Variety.mapPoints (schubertCellOfLE G u w huw) q)) := by
  dsimp only
  have hlo := levi_orbit_codimension_lower G I u q h hq
  have htor := schubert_torus_complexity G (leftParabolicRepresentative G.rootBase I u)
  have htorZ := congrArg (fun n : ℕ => (n : ℤ)) htor
  rw [Nat.cast_sub (supportCard_le_length _ _)] at htorZ
  have hlen : (weylCoxeterSystem G.rootBase).length u =
      (weylCoxeterSystem G.rootBase).length (leftParabolicFactor G.rootBase I u) +
      (weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I u) := by
    simpa only [weylCoxeterSystem_length] using
      RootInversionCount.leftParabolic_decomposition G.rootBase I u
  have hcell : ((weylCoxeterSystem G.rootBase).length u : ℤ) -
      supportCard (weylCoxeterSystem G.rootBase)
        (leftParabolicRepresentative G.rootBase I u) -
      (weylCoxeterSystem G.rootBase).length (longestParabolicElement G.rootBase I) ≤
      orbitCodim (leviBorelVariety G I) (schubertCell G u) q := by
    omega
  refine ⟨hcell, ?_⟩
  have hamb := schubertLowerOrbitCodim G I u w huw q
  rw [schubertLowerCellCodim_eq] at hamb
  omega

/-- The two Levi--Borel orbit codimension bounds over the complex numbers. -/
theorem levi_orbit_codimension_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (u w : G.weylGroup)
    (huw : WeylBruhatLE G.rootBase u w) (q : (schubertCell G u).points)
    (h : (heart G I u).points)
    (hq : Variety.mapPoints (heartCellInclusion G I u) h ∈
      MulAction.orbit (leviBorelVariety G I).points q) :
    let cs := weylCoxeterSystem G.rootBase
    let d := leftParabolicRepresentative G.rootBase I u
    let n := longestParabolicElement G.rootBase I
    ((cs.length u : ℤ) - supportCard cs d - cs.length n ≤
      orbitCodim (leviBorelVariety G I) (schubertCell G u) q) ∧
    ((cs.length w : ℤ) - supportCard cs d - cs.length n ≤
      orbitCodim (leviBorelVariety G I) (schubertVariety G w)
        (Variety.mapPoints (schubertCellOfLE G u w huw) q)) :=
  levi_orbit_codimension_bounds G I u w huw q h hq

end SchubertOrbits
