import OrbitComplexity.Paper.Heart.Meeting
import OrbitComplexity.Paper.Heart.OrbitTransport

/-! # Surjections from torus orbits to Levi--Borel orbits

Every Levi--Borel orbit in a Schubert cell meets the heart. Inclusion and parabolic
translation therefore induce surjective maps on the orbit quotients.
-/

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

/-- The map from torus orbits of the heart to Levi--Borel orbits of the Schubert cell. -/
def heartLeviOrbitMap (I : Set G.rootBase.support) (w : G.weylGroup) :
    MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points →
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points :=
  Quotient.map (Variety.mapPoints (heartCellInclusion G I w)) (by
    intro h₁ h₂ he
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at he ⊢
    obtain ⟨t, ht⟩ := he
    exact ⟨torusLeviBorelPoint G I t, (heartCell_torus_smul G I w t h₂).symm.trans
      (congrArg (Variety.mapPoints (heartCellInclusion G I w)) ht)⟩)

/-- The heart orbit map sends a representative to its closed cell inclusion. -/
theorem heartLeviOrbitMap_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    heartLeviOrbitMap G I w ⟦h⟧ = ⟦Variety.mapPoints (heartCellInclusion G I w) h⟧ := rfl

/-- Every Levi--Borel cell orbit is represented by a torus orbit of the heart. -/
theorem heartLeviOrbitMap_surjective (I : Set G.rootBase.support) (w : G.weylGroup) :
    Function.Surjective (heartLeviOrbitMap G I w) := by
  intro x
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

/-- Forward parabolic translation maps minimal-cell torus orbits to Levi--Borel cell orbits. -/
def cellLeviOrbitMap (I : Set G.rootBase.support) (w : G.weylGroup) :
    MulAction.orbitRel.Quotient (torusVariety G).points
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points →
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points :=
  heartLeviOrbitMap G I w ∘ cellHeartOrbitEquiv G I w

/-- The minimal-cell orbit map is forward translation into the heart followed by inclusion. -/
theorem cellLeviOrbitMap_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
    cellLeviOrbitMap G I w ⟦x⟧ =
      ⟦Variety.mapPoints (heartCellInclusion G I w)
        (Variety.mapPoints (heartTranslationIso G I w).hom x)⟧ := rfl

/-- Every Levi--Borel cell orbit comes from an ordinary torus orbit of the minimal cell. -/
theorem cellLeviOrbitMap_surjective (I : Set G.rootBase.support) (w : G.weylGroup) :
    Function.Surjective (cellLeviOrbitMap G I w) :=
  (heartLeviOrbitMap_surjective G I w).comp (cellHeartOrbitEquiv G I w).surjective

end SchubertOrbits
