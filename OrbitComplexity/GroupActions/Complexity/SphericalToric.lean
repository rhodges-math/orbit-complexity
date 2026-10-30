import OrbitComplexity.GroupActions.Complexity.TorusBorel

/-! # Spherical and toric varieties

Sphericality means irreducibility, normality and zero complexity. A torus is its own Borel
subgroup, so its spherical varieties are precisely the toric varieties. On an irreducible
variety, the zero-complexity condition is equivalent to a dense torus orbit.

## Main results

* `GroupActions.spherical_toric_definition`: the definitions and their torus specialization.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

universe u

/-- Sphericality specializes to toricity because a torus is its own Borel subgroup. -/
theorem spherical_toric_definition {K : Type u} [Field K] [IsAlgClosed K]
    (G : ReductiveGroups.ReductiveGroupData K) :
    (∀ (X : Variety K) [ModObj (reductiveVariety G).toOver X.toOver],
      IsSpherical G X ↔ IrreducibleSpace X.scheme ∧ X.IsNormal ∧ complexity G X = 0) ∧
    TauCeti.HopfIdeal.IsBorel K G.torusAlgebra.obj ⊥ ∧
    ∀ (Y : Variety K) [ModObj (torusVariety G).toOver Y.toOver]
      [IrreducibleSpace Y.scheme],
      letI : ModObj (reductiveVariety G.torusData).toOver Y.toOver :=
        inferInstanceAs (ModObj (torusVariety G).toOver Y.toOver)
      torusComplexity G Y = complexity G.torusData Y ∧
        (IsToricVariety G Y ↔ IsSpherical G.torusData Y) ∧
        (IsToricVariety G Y ↔ Y.IsNormal ∧
          ∃ y : Y.points, Dense (Y.pointMap '' MulAction.orbit (torusVariety G).points y)) := by
  refine ⟨fun _ _ ↦ Iff.rfl, torus_isOwnBorel G, ?_⟩
  intro Y _ _
  exact ⟨torusComplexity_eq_complexity G Y, isToricVariety_iff_isSpherical G Y,
    isToricVariety_iff_normal_dense G Y⟩

end GroupActions
