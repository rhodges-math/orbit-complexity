import OrbitComplexity.Paper.Heart.Meeting
import OrbitComplexity.Paper.Heart.OrbitTransport
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFactors

/-! # Levi--Borel orbit correspondences

When the prescribed simple roots are left descents, a Levi--Borel orbit intersects
the heart in one torus orbit. The resulting quotient equivalence also identifies
the torus orbits of the minimal parabolic cell.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def torusLeviBorelPoint (I : Set G.rootBase.support)
    (t : (torusVariety G).points) : (leviBorelVariety G I).points :=
  (leviBorelPointsMulEquiv G I).symm
    ⟨torusPointsMulEquiv G t, G.torus_le_leviBorelPoints I
      (torusPointsMulEquiv G t).property⟩

private theorem torusLeviBorel_smul (I : Set G.rootBase.support)
    (t : (torusVariety G).points) (q : (flagVariety G).points) :
    torusLeviBorelPoint G I t • q = t • q := by
  obtain ⟨f, rfl⟩ := (flagVarietyPointsEquiv G).surjective q
  rw [leviBorelFlag_smul, torusFlag_smul, flagVarietyAction_points]
  simp only [torusLeviBorelPoint, MulEquiv.apply_symm_apply]

private theorem heartCell_torus_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : (torusVariety G).points) (h : (heart G I w).points) :
    Variety.mapPoints (heartCellInclusion G I w) (t • h) =
      torusLeviBorelPoint G I t • Variety.mapPoints (heartCellInclusion G I w) h := by
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
  rw [← Variety.mapPoints_comp, heartCellInclusion_comp, leviBorelCell_smul,
    ← Variety.mapPoints_comp, heartCellInclusion_comp, torusLeviBorel_smul]
  exact heart_torus_smul G I w t h

private theorem leviBorel_torus_parabolic (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (b : G.points) (hb : b ∈ G.leviBorelPoints I) :
    ∃ t ∈ G.torusPoints, ∃ u ∈ G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _), t * u = b := by
  obtain ⟨t, ht, u, hu, he⟩ := G.leviBorel_exists_torus_mul I b hb
  refine ⟨t, ht, u, ?_, he⟩
  have ha := ((leftFactor_longest_iff G.rootBase I w).2).mpr hI
  have hroot : leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) =
      leviPositiveRoots G.rootBase I := by rw [ha, leftRootInv_longestParabolic]
  simpa only [hroot] using hu

/-- A Levi--Borel orbit meets the heart in precisely one ordinary torus orbit. -/
theorem heart_torus_orbit_iff (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h₁ h₂ : (heart G I w).points) :
    (∃ t : (torusVariety G).points, t • h₁ = h₂) ↔
      ∃ b : (leviBorelVariety G I).points,
        b • Variety.mapPoints (heartCellInclusion G I w) h₁ =
          Variety.mapPoints (heartCellInclusion G I w) h₂ := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨torusLeviBorelPoint G I t, (heartCell_torus_smul G I w t h₁).symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨t, ht, u, hu, htu⟩ := leviBorel_torus_parabolic G I w hI
      (leviBorelPointsMulEquiv G I b) (leviBorelPointsMulEquiv G I b).property
    have he := congrArg (Variety.mapPoints (schubertCellInclusion G w)) hb
    rw [leviBorelCell_smul, ← Variety.mapPoints_comp, heartCellInclusion_comp,
      ← Variety.mapPoints_comp, heartCellInclusion_comp, leviBorelFlag_smul] at he
    have he' : reductivePointsMulEquiv G (t * 1 * u) •
        Variety.mapPoints (heartInclusion G I w) h₁ =
      Variety.mapPoints (heartInclusion G I w) h₂ := by
      simpa only [mul_one, htu] using he
    obtain ⟨_, htH⟩ := heart_factor_eq_one G I w t 1 u ht (Subgroup.one_mem _) hu
      _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ he'
    let z : (torusVariety G).points := (torusPointsMulEquiv G).symm ⟨t, ht⟩
    refine ⟨z, ?_⟩
    apply Variety.mapPoints_injective_of_mono (heartInclusion G I w)
    rw [heart_torus_smul]
    have hz : z • Variety.mapPoints (heartInclusion G I w) h₁ =
        reductivePointsMulEquiv G t • Variety.mapPoints (heartInclusion G I w) h₁ := by
      obtain ⟨f, hf⟩ := (flagVarietyPointsEquiv G).surjective
        (Variety.mapPoints (heartInclusion G I w) h₁)
      rw [← hf, torusFlag_smul, ← flagVarietyAction_points]
      have hz' : (torusPointsMulEquiv G z : G.points) = t := by
        exact congrArg Subtype.val ((torusPointsMulEquiv G).apply_symm_apply ⟨t, ht⟩)
      rw [hz']
    exact hz.trans (by simpa only [mul_one] using htH)

private theorem heartLevi_orbitRel_iff (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h₁ h₂ : (heart G I w).points) :
    MulAction.orbitRel (torusVariety G).points (heart G I w).points h₁ h₂ ↔
      MulAction.orbitRel (leviBorelVariety G I).points (schubertCell G w).points
        (Variety.mapPoints (heartCellInclusion G I w) h₁)
        (Variety.mapPoints (heartCellInclusion G I w) h₂) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact heart_torus_orbit_iff G I w hI h₂ h₁

private def heartLeviOrbitMap (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i)) :
    MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points →
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points :=
  Quotient.map (Variety.mapPoints (heartCellInclusion G I w))
    (fun h₁ h₂ h => (heartLevi_orbitRel_iff G I w hI h₁ h₂).mp h)

private theorem heartLeviOrbitMap_bijective (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i)) :
    Function.Bijective (heartLeviOrbitMap G I w hI) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h h₁ =>
      induction y using Quotient.inductionOn with
      | h h₂ =>
        intro he
        apply Quotient.sound
        exact (heartLevi_orbitRel_iff G I w hI h₁ h₂).mpr (Quotient.exact he)
  · intro x
    induction x using Quotient.inductionOn with
    | h q =>
      obtain ⟨b, hheart⟩ := leviBorel_orbit_meets_heart G I w q
      obtain ⟨h, hh⟩ := hheart
      have hc : Variety.mapPoints (heartCellInclusion G I w) h = b • q := by
        apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
        rw [← Variety.mapPoints_comp, heartCellInclusion_comp]
        exact hh
      refine ⟨⟦h⟧, Quotient.sound ?_⟩
      exact (MulAction.orbitRel_apply).mpr (MulAction.mem_orbit_iff.mpr ⟨b, hc.symm⟩)

/-- Heart torus orbits correspond bijectively to Levi--Borel Schubert-cell orbits. -/
def heartLeviOrbitEquiv (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i)) :
    MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points ≃
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points :=
  Equiv.ofBijective (heartLeviOrbitMap G I w hI) (heartLeviOrbitMap_bijective G I w hI)

/-- The heart-to-cell orbit equivalence sends a point to its closed cell inclusion. -/
theorem heartLeviOrbitEquiv_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) :
    heartLeviOrbitEquiv G I w hI ⟦h⟧ = ⟦Variety.mapPoints (heartCellInclusion G I w) h⟧ := rfl

/-- Minimal-cell torus orbits correspond to Levi--Borel orbits in the original cell. -/
def cellLeviOrbitEquiv (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i)) :
    MulAction.orbitRel.Quotient (torusVariety G).points
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points ≃
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points :=
  (cellHeartOrbitEquiv G I w).trans (heartLeviOrbitEquiv G I w hI)

/-- The minimal-cell orbit correspondence is forward parabolic translation into the heart. -/
theorem cellLeviOrbitEquiv_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (x : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
    cellLeviOrbitEquiv G I w hI ⟦x⟧ =
      ⟦Variety.mapPoints (heartCellInclusion G I w)
        (Variety.mapPoints (heartTranslationIso G I w).hom x)⟧ := rfl

end SchubertOrbits
