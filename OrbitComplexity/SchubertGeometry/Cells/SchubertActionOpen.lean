import OrbitComplexity.GroupActions.Actions.SubgroupOpen
import OrbitComplexity.SchubertGeometry.FlagVariety.BorelProduct
import OrbitComplexity.SchubertGeometry.Cells.OppositeActions

/-! # Open action families on Schubert varieties

Multiplication of the two Borel factors is smooth. The stability of each Schubert closure
under its defining Borel makes the other Borel action family open onto the flag variety.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem flagOrbit_surjective :
    Surjective (Variety.orbitMorphism (reductiveVariety G) (flagVariety G)
      (flagVarietyPointsEquiv G (baseFlag G))).left := by
  have he : Variety.orbitMorphism (reductiveVariety G) (flagVariety G)
      (flagVarietyPointsEquiv G (baseFlag G)) = flagQuotientMorphism G := by
    apply Variety.mapPoints_injective (X := reductiveVariety G) (Y := flagVariety G)
    funext q
    obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective q
    rw [Variety.mapPoints_orbitMorphism, flagVarietyAction_points]
    change flagVarietyPointsEquiv G (g • baseFlag G) =
      Variety.mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G g)
    rw [flagQuotientMorphism_points]
    apply congrArg (flagVarietyPointsEquiv G)
    change flagProjection G (g * 1) = flagProjection G g
    rw [mul_one]
  rw [he]
  exact inferInstanceAs (Surjective (flagQuotient G))

/-- The Borel action family on an opposite Schubert variety is open into the flag variety. -/
theorem oppositeSchubert_borel_open (u : G.weylGroup) :
    IsOpenMap (((borelVariety G).toOver ◁ oppositeSchubertInclusion G u) ≫
      γ[(borelVariety G).toOver, (flagVariety G).toOver]).left := by
  have hm : Smooth (((borelInclusion G ⊗ₘ oppositeBorelInclusion G) ≫
      μ[(reductiveVariety G).toOver]).left) := by
    have he : (borelInclusion G ⊗ₘ oppositeBorelInclusion G) ≫
        μ[(reductiveVariety G).toOver] = borelOppositeMul G := by
      rw [borelOppositeMul, Hom.mul_def, ← lift_fst_comp_snd_comp]
    rw [he]
    infer_instance
  have ho := actionFamily_open_of_smooth_mul (borelVariety G) (oppositeBorelVariety G)
    (reductiveVariety G) (flagVariety G) (oppositeSchubertVariety G u)
    (borelInclusion G) (oppositeBorelInclusion G) (oppositeSchubertInclusion G u)
    (by exact oppositeSchubertBorelEquivariant G u) hm
    (flagVarietyPointsEquiv G (baseFlag G)) (flagOrbit_surjective G)
  change IsOpenMap (((borelVariety G).toOver ◁ oppositeSchubertInclusion G u) ≫
    (borelInclusion G ▷ (flagVariety G).toOver) ≫
      γ[(reductiveVariety G).toOver, (flagVariety G).toOver]).left
  rwa [← tensorHom_def'_assoc]

/-- The opposite Borel action family on a Schubert variety is open into the flag variety. -/
theorem schubert_oppositeBorel_open (v : G.weylGroup) :
    IsOpenMap (((oppositeBorelVariety G).toOver ◁ schubertInclusion G v) ≫
      γ[(oppositeBorelVariety G).toOver, (flagVariety G).toOver]).left := by
  have hm : Smooth (((oppositeBorelInclusion G ⊗ₘ borelInclusion G) ≫
      μ[(reductiveVariety G).toOver]).left) := by
    have he : (oppositeBorelInclusion G ⊗ₘ borelInclusion G) ≫
        μ[(reductiveVariety G).toOver] = oppositeBorelMul G := by
      rw [oppositeBorelMul, Hom.mul_def, ← lift_fst_comp_snd_comp]
    rw [he]
    infer_instance
  have ho := actionFamily_open_of_smooth_mul (oppositeBorelVariety G) (borelVariety G)
    (reductiveVariety G) (flagVariety G) (schubertVariety G v)
    (oppositeBorelInclusion G) (borelInclusion G) (schubertInclusion G v)
    (by exact schubertBorelEquivariant G v) hm
    (flagVarietyPointsEquiv G (baseFlag G)) (flagOrbit_surjective G)
  change IsOpenMap (((oppositeBorelVariety G).toOver ◁ schubertInclusion G v) ≫
    (oppositeBorelInclusion G ▷ (flagVariety G).toOver) ≫
      γ[(reductiveVariety G).toOver, (flagVariety G).toOver]).left
  rwa [← tensorHom_def'_assoc]

end
end SchubertGeometry
