import OrbitComplexity.Paper.Heart.Decomposition
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.GroupActions.Actions.Restriction

/-!
# The heart as a locally closed flag subvariety

The heart is the reduced locally closed orbit of the conjugated minimal-factor
subgroup at the Weyl flag. Root coordinates identify that subgroup with the heart.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private instance rootFlagAction (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    ModObj (rootSubsetVariety G R hR).toOver (flagVariety G).toOver :=
  Mod.scalarRestriction (rootSubsetInclusion G R hR) (flagVariety G).toOver

/-- The I-heart is the reduced locally closed subvariety Vd wB of the flag variety. -/
def heart (I : Set G.rootBase.support) (w : G.weylGroup) : Variety K :=
  orbitVariety (Vd.variety G I w) (flagVariety G) (weylFlagPoint G w)

/-- The inclusion of the I-heart into the flag variety. -/
def heartInclusion (I : Set G.rootBase.support) (w : G.weylGroup) :
    (heart G I w).toOver ⟶ (flagVariety G).toOver :=
  orbitInclusion (Vd.variety G I w) (flagVariety G) (weylFlagPoint G w)

/-- The I-heart is a locally closed subvariety of the flag variety. -/
instance heartInclusion_isPreimmersion (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsPreimmersion (heartInclusion G I w).left := by
  change IsPreimmersion (orbitInclusion (Vd.variety G I w) (flagVariety G)
    (weylFlagPoint G w)).left
  infer_instance

/-- Root coordinates map a point of Vd to its flag in the heart. -/
def heartRootMorphism (I : Set G.rootBase.support) (w : G.weylGroup) :
    (Vd.variety G I w).toOver ⟶ (flagVariety G).toOver :=
  Vd.inclusion G I w ≫ schubertRootMorphism G w

/-- The root-coordinate parametrization of the heart is a locally closed embedding. -/
instance heartRootMorphism_isPreimmersion (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsPreimmersion (heartRootMorphism G I w).left := by
  change IsPreimmersion ((Vd.inclusion G I w).left ≫ (schubertRootMorphism G w).left)
  infer_instance

/-- The root-coordinate heart map is the ambient orbit morphism restricted to Vd. -/
theorem heartRootMorphism_eq (I : Set G.rootBase.support) (w : G.weylGroup) :
    heartRootMorphism G I w =
      rootSubsetInclusion G (heartRootIndices G I w) (heartRootIndices_closed G I w) ≫
        Variety.orbitMorphism (reductiveVariety G) (flagVariety G) (weylFlagPoint G w) := by
  change (Vd.inclusion G I w ≫ rootSubsetInclusion G
    (leftRootInversionIndices G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) ≫ _) = _
  rw [← Category.assoc, Vd.inclusion_comp]

/-- The heart map sends a subgroup point to its product with the Weyl flag. -/
theorem heartRootMorphism_points (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (Vd.variety G I w).points) :
    Variety.mapPoints (heartRootMorphism G I w) x =
      flagVarietyPointsEquiv G (flagProjection G
        ((rootSubsetPointsMulEquiv G _ (heartRootIndices_closed G I w) x : G.points) *
          G.weylPoint w)) := by
  rw [heartRootMorphism_eq, Variety.mapPoints_comp, Variety.mapPoints_orbitMorphism,
    rootSubsetInclusion_points]
  exact flagVarietyAction_points G _ _

/-- The heart parametrization is the orbit map for the restricted Vd action. -/
theorem heartRootMorphism_orbit (I : Set G.rootBase.support) (w : G.weylGroup) :
    heartRootMorphism G I w =
      Variety.orbitMorphism (Vd.variety G I w) (flagVariety G) (weylFlagPoint G w) := by
  apply Variety.mapPoints_injective
  funext x
  rw [heartRootMorphism_eq, Variety.mapPoints_comp, Variety.mapPoints_orbitMorphism,
    Variety.mapPoints_orbitMorphism]
  exact (Variety.restricted_smul
    (rootSubsetInclusion G _ (heartRootIndices_closed G I w))
    (flagVariety G) x (weylFlagPoint G w)).symm

/-- Vd root coordinates identify the subgroup variety with the I-heart. -/
def heartIso (I : Set G.rootBase.support) (w : G.weylGroup) :
    (Vd.variety G I w).toOver ≅ (heart G I w).toOver :=
  Variety.pointImageIso (heartRootMorphism G I w) (heartInclusion G I w) (by
    change Set.range (Variety.mapPoints (heartRootMorphism G I w)) =
      Set.range (Variety.mapPoints (orbitInclusion (Vd.variety G I w)
        (flagVariety G) (weylFlagPoint G w)))
    rw [heartRootMorphism_orbit]
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨Variety.mapPoints (orbitProjection (Vd.variety G I w) (flagVariety G)
        (weylFlagPoint G w)) p, ?_⟩
      rw [← Variety.mapPoints_comp]
      exact congrArg (fun f => Variety.mapPoints f p)
        (orbitProjection_fac (Vd.variety G I w) (flagVariety G) (weylFlagPoint G w))
    · rintro ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := orbitProjection_points_surjective (Vd.variety G I w)
        (flagVariety G) (weylFlagPoint G w) p
      refine ⟨x, ?_⟩
      rw [← Variety.mapPoints_comp]
      exact (congrArg (fun f => Variety.mapPoints f x)
        (orbitProjection_fac (Vd.variety G I w) (flagVariety G)
          (weylFlagPoint G w))).symm)

end SchubertOrbits
