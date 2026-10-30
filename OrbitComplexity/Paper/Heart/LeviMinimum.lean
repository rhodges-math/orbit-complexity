import OrbitComplexity.Paper.Heart.LeviOrbitStatements
import OrbitComplexity.GroupActions.Complexity.OrbitCodimension

/-! # Minimum cell orbit codimension

A Levi action identifies the minimum Levi--Borel orbit codimension of a Schubert
cell with the ordinary torus minimum in the minimal parabolic cell.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem orbitCodim_smul (H X : Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (b : H.points) (x : X.points) :
    orbitCodim H X (b • x) = orbitCodim H X x := by
  simp only [orbitCodim, orbitNatDim, orbitDim, MulAction.orbit_smul]

private theorem heartLevi_minOrbitCodim (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i)) :
    minOrbitCodim (leviBorelVariety G I) (schubertCell G w) =
      minOrbitCodim (torusVariety G) (heart G I w) := by
  let d := leftParabolicRepresentative G.rootBase I w
  let x : (schubertCell G d).points := Variety.mapPoints (schubertCellIso G d).hom 1
  let h : (heart G I w).points := Variety.mapPoints (heartTranslationIso G I w).hom x
  have : Nonempty (heart G I w).scheme := ⟨(heart G I w).pointMap h⟩
  have : Nonempty (schubertCell G w).scheme := ⟨(schubertCell G w).pointMap
    (Variety.mapPoints (heartCellInclusion G I w) h)⟩
  apply le_antisymm
  · obtain ⟨a, ha⟩ := exists_orbitCodim_eq (torusVariety G) (heart G I w)
    have hmin := minOrbitCodim_le (leviBorelVariety G I) (schubertCell G w)
      (Variety.mapPoints (heartCellInclusion G I w) a)
    rw [heartLeviOrbitCodim G I w hI a, ha] at hmin
    exact_mod_cast hmin
  · obtain ⟨q, hq⟩ := exists_orbitCodim_eq (leviBorelVariety G I) (schubertCell G w)
    obtain ⟨b, a, ha⟩ := leviBorel_orbit_meets_heart G I w q
    have he : Variety.mapPoints (heartCellInclusion G I w) a = b • q := by
      apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
      rw [← Variety.mapPoints_comp, heartCellInclusion_comp]
      exact ha
    have hmin := minOrbitCodim_le (torusVariety G) (heart G I w) a
    rw [← heartLeviOrbitCodim G I w hI a, he, orbitCodim_smul, hq] at hmin
    exact_mod_cast hmin

/-- If the Levi acts, the minimum Levi--Borel cell codimension equals the minimal-cell torus one. -/
theorem levi_cell_minOrbitCodim (I : Set G.rootBase.support) (w : G.weylGroup)
    (hact : ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) :
    minOrbitCodim (leviBorelVariety G I) (schubertCell G w) =
      minOrbitCodim (torusVariety G)
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) := by
  have hdesc := (levi_schubert_action_iff G I w).mp hact
  have ha := (complement_equivalences G I w).2.2.2.mp hdesc
  have hI := (leftFactor_longest_iff G.rootBase I w).2.mp ha
  exact (heartLevi_minOrbitCodim G I w hI).trans (heart_minOrbitCodim G I w)

/-- The minimum cell orbit codimension comparison over the complex numbers. -/
theorem levi_cell_minOrbitCodim_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup)
    (hact : ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) :
    minOrbitCodim (leviBorelVariety G I) (schubertCell G w) =
      minOrbitCodim (torusVariety G)
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) :=
  levi_cell_minOrbitCodim G I w hact

end SchubertOrbits
