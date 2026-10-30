import OrbitComplexity.SchubertGeometry.Levi.Subgroup
import OrbitComplexity.SchubertGeometry.Levi.Borel
import OrbitComplexity.SchubertGeometry.FlagVariety.Action
import OrbitComplexity.GroupActions.Actions.Restriction

/-!
# Standard Levi actions on the flag variety

The closed group inclusions restrict the reductive flag action to the
standard Levi and its intersection with the Borel.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The standard Levi acts algebraically on the flag variety by left multiplication. -/
instance leviFlagAction (I : Set G.rootBase.support) :
    ModObj (leviVariety G I).toOver (flagVariety G).toOver :=
  Mod.scalarRestriction (leviInclusion G I) (flagVariety G).toOver

/-- Levi multiplication on flags agrees with the ambient reductive-group action. -/
theorem leviFlag_smul (I : Set G.rootBase.support)
    (l : (leviVariety G I).points) (q : (flagVariety G).points) :
    l • q = reductivePointsMulEquiv G (leviPointsMulEquiv G I l) • q := by
  exact (Variety.restricted_smul (leviInclusion G I) (flagVariety G) l q).trans
    (congrArg (fun g => g • q) (leviInclusion_points G I l))

/-- The Levi--Borel subgroup acts algebraically on the flag variety. -/
instance leviBorelFlagAction (I : Set G.rootBase.support) :
    ModObj (leviBorelVariety G I).toOver (flagVariety G).toOver :=
  Mod.scalarRestriction (leviBorelInclusion G I) (flagVariety G).toOver

/-- Levi--Borel multiplication on flags agrees with the ambient group action. -/
theorem leviBorelFlag_smul (I : Set G.rootBase.support)
    (b : (leviBorelVariety G I).points) (q : (flagVariety G).points) :
    b • q = reductivePointsMulEquiv G (leviBorelPointsMulEquiv G I b) • q := by
  exact (Variety.restricted_smul (leviBorelInclusion G I) (flagVariety G) b q).trans
    (congrArg (fun g => g • q) (leviBorelInclusion_points G I b))

end SchubertGeometry
