import OrbitComplexity.GroupActions.Tori.SupportMaps
import OrbitComplexity.GroupActions.Tori.Coordinates
import OrbitComplexity.GroupActions.Varieties.AffineCoordinates
import OrbitComplexity.GroupActions.Varieties.AffineImages
import OrbitComplexity.GroupActions.Varieties.TorusVariety
import OrbitComplexity.GroupActions.Actions.Orbits

/-! # Orbit dimensions from coordinate characters

For a torus action whose affine coordinates scale by lattice characters, the orbit dimension
is the real dimension of the span of the weights at nonzero coordinates. The dimension is
computed from the coordinate image algebra of the orbit parametrization.

## Main results

* `GroupActions.torus_orbit_dim`: the Krull dimension of an orbit from its supported weights.
-/

open CategoryTheory AlgebraicGeometry Multiplicative

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

private theorem orbitTorusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] orbitTorusReduced

variable {ι : Type u} [Fintype ι]

/-- The weight monomials with prescribed scalars parametrize points of affine space. -/
def torusWeightMap (w : ι → G.torusIndex →₀ ℤ) (v : ι → K) :
    (torusVariety G).toOver ⟶ (affineSpaceVariety K ι).toOver :=
  affineMorphism ((torusCoordinateEquiv G).symm.toAlgHom.comp (weightedPolynomialMap w v))

/-- Coordinates of the weight map evaluate the corresponding torus character. -/
theorem torusWeightMap_coordinate (w : ι → G.torusIndex →₀ ℤ) (v : ι → K)
    (t : (torusVariety G).points) (i : ι) :
    affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints (torusWeightMap G w v) t) i =
      v i * affinePointsEquiv.symm t
        ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (ofAdd (w i)) 1)) := by
  calc
    _ = affineVarietyPointsEquiv K G.torusAlgebra t
        (((torusCoordinateEquiv G).symm.toAlgHom.comp (weightedPolynomialMap w v))
          (MvPolynomial.X i)) := affineMorphism_coordinate _ t i
    _ = _ := by
      simp only [AlgHom.comp_apply, weightedPolynomialMap_X, map_smul, smul_eq_mul]
      rfl

variable [IsAlgClosed K]

/-- A torus weight map has image dimension equal to its supported real character rank. -/
theorem torusWeightMap_image_dim (w : ι → G.torusIndex →₀ ℤ) (v : ι → K) :
    (affineSpaceVariety K ι).subsetDim
      (Set.range (Variety.mapPoints (torusWeightMap G w v))) =
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun (i : {i // v i ≠ 0}) k ↦ (w i.val k : ℝ)))) : WithBot ℕ∞) := by
  let := G.finiteIndex
  calc
    _ = ringKrullDim
        ((torusCoordinateEquiv G).symm.toAlgHom.comp (weightedPolynomialMap w v)).range :=
      affineMorphism_image_dim _
    _ = ringKrullDim (weightedPolynomialMap w v).range := by
      rw [AlgHom.range_comp]
      exact (ringKrullDim_eq_of_ringEquiv
        ((weightedPolynomialMap w v).range.equivMapOfInjective
          (torusCoordinateEquiv G).symm.toAlgHom
          (torusCoordinateEquiv G).symm.injective).toRingEquiv).symm
    _ = _ := ringKrullDim_weighted_real w v

variable [ModObj (torusVariety G).toOver (affineSpaceVariety K ι).toOver]

/-- A coordinate torus orbit has the real span dimension of its nonzero-coordinate weights. -/
theorem torus_orbit_dim (w : ι → G.torusIndex →₀ ℤ) (x : (affineSpaceVariety K ι).points)
    (h : ∀ (t : (torusVariety G).points) (i : ι),
      affineSpaceVarietyPointsEquiv K ι (t • x) i =
        affineSpaceVarietyPointsEquiv K ι x i * affinePointsEquiv.symm t
          ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (ofAdd (w i)) 1))) :
    orbitDim (torusVariety G) (affineSpaceVariety K ι) x =
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun (i : {i // affineSpaceVarietyPointsEquiv K ι x i ≠ 0}) k ↦
          (w i.val k : ℝ)))) : WithBot ℕ∞) := by
  let v := affineSpaceVarietyPointsEquiv K ι x
  have hm (t : (torusVariety G).points) :
      Variety.mapPoints (torusWeightMap G w v) t = t • x := by
    apply (affineSpaceVarietyPointsEquiv K ι).injective
    funext i
    exact (torusWeightMap_coordinate G w v t i).trans (h t i).symm
  have ho : MulAction.orbit (torusVariety G).points x =
      Set.range (Variety.mapPoints (torusWeightMap G w v)) := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_range]
    exact exists_congr fun t ↦ by rw [hm t]
  calc
    _ = (affineSpaceVariety K ι).subsetDim
        (Set.range (Variety.mapPoints (torusWeightMap G w v))) :=
      congrArg (affineSpaceVariety K ι).subsetDim ho
    _ = _ := torusWeightMap_image_dim G w v

end

end GroupActions
