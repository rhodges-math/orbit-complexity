import OrbitComplexity.Paper.Heart.CodimensionBounds
import OrbitComplexity.Paper.Heart.LeviClosureComplexity
import OrbitComplexity.Paper.Heart.ComplementEquivalences
import OrbitComplexity.SchubertGeometry.Parabolics.LeftOrder

/-! # Levi complexity from orbit codimensions and parabolic support -/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
  Topology BruhatIntervals
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem orbit_meets_heart (I : Set G.rootBase.support) (u : G.weylGroup)
    (q : (schubertCell G u).points) :
    ∃ h : (heart G I u).points,
      Variety.mapPoints (heartCellInclusion G I u) h ∈
        MulAction.orbit (leviBorelVariety G I).points q := by
  obtain ⟨b, h, hh⟩ := leviBorel_orbit_meets_heart G I u q
  refine ⟨h, MulAction.mem_orbit_iff.mpr ⟨b, ?_⟩⟩
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G u)
  rw [← Variety.mapPoints_comp, heartCellInclusion_comp]
  exact hh.symm

private theorem lower_points_cover (w : G.weylGroup) (q : (schubertVariety G w).points) :
    ∃ u : G.weylGroup, ∃ huw : WeylBruhatLE G.rootBase u w,
      ∃ p : (schubertCell G u).points,
        Variety.mapPoints (schubertCellOfLE G u w huw) p = q := by
  have hq : Variety.mapPoints (schubertInclusion G w) q ∈
      Set.range (Variety.mapPoints (schubertInclusion G w)) := ⟨q, rfl⟩
  rw [schubertVariety_points_cells] at hq
  obtain ⟨u, huw, p, hp⟩ := Set.mem_iUnion₂.mp hq
  refine ⟨u, huw, p, ?_⟩
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  rw [← Variety.mapPoints_comp, schubertCellOfLE_comp]
  exact hp

private theorem orbit_codimension_lower (I : Set G.rootBase.support) (w : G.weylGroup)
    (hdesc : I ⊆ leftDescents (weylCoxeterSystem G.rootBase) w)
    (q : (schubertVariety G w).points) :
    ((weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I w) : ℤ) -
      supportCard (weylCoxeterSystem G.rootBase)
        (leftParabolicRepresentative G.rootBase I w) ≤
      orbitCodim (leviBorelVariety G I) (schubertVariety G w) q := by
  obtain ⟨u, huw, p, rfl⟩ := lower_points_cover G w q
  obtain ⟨h, hh⟩ := orbit_meets_heart G I u p
  have hb := (levi_orbit_codimension_bounds G I u w huw p h hh).2
  have hs := leftParabolic_supportCard_mono G.rootBase I u w huw
  have ha := (complement_equivalences G I w).2.2.2.mp hdesc
  have hlen : (weylCoxeterSystem G.rootBase).length w =
      (weylCoxeterSystem G.rootBase).length (longestParabolicElement G.rootBase I) +
      (weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I w) := by
    simpa only [weylCoxeterSystem_length, ha] using
      RootInversionCount.leftParabolic_decomposition G.rootBase I w
  omega

private theorem minimum_lower (I : Set G.rootBase.support) (w : G.weylGroup)
    (hdesc : I ⊆ leftDescents (weylCoxeterSystem G.rootBase) w) :
    (weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I w) -
      supportCard (weylCoxeterSystem G.rootBase)
        (leftParabolicRepresentative G.rootBase I w) ≤
      minOrbitCodim (leviBorelVariety G I) (schubertVariety G w) := by
  obtain ⟨q, hq⟩ := exists_orbitCodim_eq (leviBorelVariety G I) (schubertVariety G w)
  have hl := orbit_codimension_lower G I w hdesc q
  have hs := supportCard_le_length (weylCoxeterSystem G.rootBase)
    (leftParabolicRepresentative G.rootBase I w)
  omega

/-- A standard Levi action has complexity equal to minimal-representative length minus support. -/
private theorem levi_complexity_formula (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      (weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I w) -
        supportCard (weylCoxeterSystem G.rootBase)
          (leftParabolicRepresentative G.rootBase I w) := by
  let : ModObj (reductiveVariety (leviGroupData G I)).toOver
      (schubertVariety G w).toOver :=
    inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
  apply le_antisymm
  · exact ((levi_complexity_eq_minimal G I w).trans
      (schubert_torus_complexity G (leftParabolicRepresentative G.rootBase I w))).le
  · exact (minimum_lower G I w ((levi_schubert_action_iff G I w).mp
      ⟨inferInstance, inferInstance⟩)).trans_eq (levi_schubert_complexity G I w).symm

/-- Levi action existence is the descent condition, and each action has the support formula. -/
theorem levi_complexity_properties (I : Set G.rootBase.support) (w : G.weylGroup) :
    ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
        I ⊆ leftDescents (weylCoxeterSystem G.rootBase) w) ∧
    (∀ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      ∀ ha : letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w),
      letI := a
      letI := ha
      letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
          (schubertVariety G w).toOver :=
        inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
      complexity (leviGroupData G I) (schubertVariety G w) =
        (weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I w) -
          supportCard (weylCoxeterSystem G.rootBase)
            (leftParabolicRepresentative G.rootBase I w)) := by
  refine ⟨levi_schubert_action_iff G I w, ?_⟩
  intro a ha
  let := a
  let := ha
  exact levi_complexity_formula G I w

/-- The Levi action criterion and Schubert complexity formula over the complex numbers. -/
theorem levi_complexity_properties_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
        I ⊆ leftDescents (weylCoxeterSystem G.rootBase) w) ∧
    (∀ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      ∀ ha : letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w),
      letI := a
      letI := ha
      letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
          (schubertVariety G w).toOver :=
        inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
      complexity (leviGroupData G I) (schubertVariety G w) =
        (weylCoxeterSystem G.rootBase).length (leftParabolicRepresentative G.rootBase I w) -
          supportCard (weylCoxeterSystem G.rootBase)
            (leftParabolicRepresentative G.rootBase I w)) :=
  levi_complexity_properties G I w

end SchubertOrbits
