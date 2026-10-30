import OrbitComplexity.GroupActions.Complexity.Basic
import OrbitComplexity.GroupActions.Complexity.Toric
import OrbitComplexity.GroupActions.Complexity.Spherical
import OrbitComplexity.GroupActions.Actions.RestrictionOrbits
import OrbitComplexity.GroupActions.Varieties.BorelPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.TorusData

/-! # The Borel subgroup of a torus

A torus is its own Borel subgroup. When the Borel defining ideal is zero, reductive-group
complexity agrees with the minimum codimension for the whole group action.

## Main results

* `GroupActions.torus_isOwnBorel`: a chosen maximal torus is its own Borel.
* `GroupActions.complexity_of_borel_bot`: a zero Borel ideal gives the whole-group minimum.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- The chosen maximal torus is its own Borel subgroup. -/
theorem torus_isOwnBorel : TauCeti.HopfIdeal.IsBorel K G.torusAlgebra.obj ⊥ :=
  ReductiveGroups.torus_isBorel_bot G.torusAlgebra G.torus_isTorus

variable [IsAlgClosed K]

private theorem borel_points_surj (hG : G.borelIdeal = ⊥) :
    Function.Surjective (Variety.mapPoints (borelInclusion G)) := by
  intro y
  let p := (reductivePointsEquiv G).symm y
  have hmem : p ∈ G.borelPoints := by
    simp only [ReductiveGroups.ReductiveGroupData.borelPoints, hG,
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup_bot]
    exact Subgroup.mem_top p
  refine ⟨(borelPointsMulEquiv G).symm ⟨p, hmem⟩, ?_⟩
  rw [borelInclusion_points, MulEquiv.apply_symm_apply]
  exact (reductivePointsEquiv G).apply_symm_apply y

variable (X : Variety K) [ModObj (reductiveVariety G).toOver X.toOver]

/-- If the Borel subgroup is the whole group, complexity is the whole-group orbit minimum. -/
theorem complexity_of_borel_bot (hG : G.borelIdeal = ⊥) :
    complexity G X = minOrbitCodim (reductiveVariety G) X :=
  Variety.restricted_minOrbitCodim (borelInclusion G) (borel_points_surj G hG) X

/-- The reductive complexity of a split torus is its whole-group orbit minimum. -/
theorem splitTorus_complexity (ι : Type u) [Finite ι]
    (Y : Variety K)
    [ModObj (reductiveVariety (ReductiveGroups.SplitTorus.groupData K ι)).toOver Y.toOver] :
    complexity (ReductiveGroups.SplitTorus.groupData K ι) Y =
      minOrbitCodim (reductiveVariety (ReductiveGroups.SplitTorus.groupData K ι)) Y :=
  complexity_of_borel_bot _ _ rfl

/-- Torus complexity is the reductive complexity of the torus regarded as its own group. -/
theorem torusComplexity_eq_complexity (Y : Variety K)
    [ModObj (torusVariety G).toOver Y.toOver] :
    letI : ModObj (reductiveVariety G.torusData).toOver Y.toOver :=
      inferInstanceAs (ModObj (torusVariety G).toOver Y.toOver)
    torusComplexity G Y = complexity G.torusData Y := by
  let : ModObj (reductiveVariety G.torusData).toOver Y.toOver :=
    inferInstanceAs (ModObj (torusVariety G).toOver Y.toOver)
  exact (complexity_of_borel_bot G.torusData Y rfl).symm

/-- A torus variety is toric exactly when it is spherical for the torus as a reductive group. -/
theorem isToricVariety_iff_isSpherical (Y : Variety K)
    [ModObj (torusVariety G).toOver Y.toOver] :
    letI : ModObj (reductiveVariety G.torusData).toOver Y.toOver :=
      inferInstanceAs (ModObj (torusVariety G).toOver Y.toOver)
    IsToricVariety G Y ↔ IsSpherical G.torusData Y := by
  let : ModObj (reductiveVariety G.torusData).toOver Y.toOver :=
    inferInstanceAs (ModObj (torusVariety G).toOver Y.toOver)
  rw [IsToricVariety, IsSpherical, torusComplexity_eq_complexity]
  rfl

end

end GroupActions
