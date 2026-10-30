import OrbitComplexity.GroupActions.Tori.OrbitRank
import OrbitComplexity.GroupActions.Actions.ImmersedOrbits

/-! # Torus orbit ranks in immersed coordinates

A locally closed immersion into affine space provides regular coordinates for an orbit.
When those coordinates scale by characters, the nonzero-coordinate weights compute its
dimension without requiring an action on the whole affine space.
-/

open CategoryTheory AlgebraicGeometry Multiplicative

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K) (X : Variety K)
  [ModObj (torusVariety G).toOver X.toOver] {ι : Type u} [Fintype ι]

/-- Immersed coordinates compute a torus orbit's Krull dimension from its supported weights. -/
theorem torus_orbit_dim_of_immersion (j : X.toOver ⟶ (affineSpaceVariety K ι).toOver)
    [IsImmersion j.left]
    (w : ι → G.torusIndex →₀ ℤ) (x : X.points)
    (h : ∀ (t : (torusVariety G).points) (i : ι),
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j (t • x)) i =
        affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j x) i * affinePointsEquiv.symm t
          ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (ofAdd (w i)) 1))) :
    orbitDim (torusVariety G) X x =
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun (i : {i // affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j x) i ≠ 0}) k ↦
          (w i.val k : ℝ)))) : WithBot ℕ∞) := by
  let v := affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j x)
  have hm (t : (torusVariety G).points) :
      Variety.mapPoints (torusWeightMap G w v) t = Variety.mapPoints j (t • x) := by
    apply (affineSpaceVarietyPointsEquiv K ι).injective
    funext i
    exact (torusWeightMap_coordinate G w v t i).trans (h t i).symm
  have ho : Variety.mapPoints j '' MulAction.orbit (torusVariety G).points x =
      Set.range (Variety.mapPoints (torusWeightMap G w v)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.mp hz
      exact ⟨t, hm t⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t • x, MulAction.mem_orbit x t, (hm t).symm⟩
  calc
    _ = (affineSpaceVariety K ι).subsetDim
        (Variety.mapPoints j '' MulAction.orbit (torusVariety G).points x) :=
      (orbit_image_dim (torusVariety G) X _ j x).symm
    _ = (affineSpaceVariety K ι).subsetDim
        (Set.range (Variety.mapPoints (torusWeightMap G w v))) :=
      congrArg (affineSpaceVariety K ι).subsetDim ho
    _ = _ := torusWeightMap_image_dim G w v


/-- Immersed coordinates compute the natural dimension of a torus orbit. -/
theorem torus_orbitNatDim_of_immersion
    (j : X.toOver ⟶ (affineSpaceVariety K ι).toOver) [IsImmersion j.left]
    (w : ι → G.torusIndex →₀ ℤ) (x : X.points)
    (h : ∀ (t : (torusVariety G).points) (i : ι),
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j (t • x)) i =
        affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j x) i * affinePointsEquiv.symm t
          ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (ofAdd (w i)) 1))) :
    orbitNatDim (torusVariety G) X x =
      Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun (i : {i // affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j x) i ≠ 0}) k ↦
          (w i.val k : ℝ)))) := by
  have hc : (orbitNatDim (torusVariety G) X x : WithBot ℕ∞) =
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun (i : {i // affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints j x) i ≠ 0}) k ↦
          (w i.val k : ℝ)))) : WithBot ℕ∞) := by
    rw [orbitNatDim_cast, torus_orbit_dim_of_immersion G X j w x h]
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hc)

end

end GroupActions
