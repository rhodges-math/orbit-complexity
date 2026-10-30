import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviIdeal
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-! # Smooth Levi groups and subgroup ideal inclusions

Reduced Levi coordinate quotients are smooth, and the torus, Borel and Levi ideals
have the inclusions induced by their point subgroups.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The reduced standard Levi coordinate algebra is smooth over the base field. -/
theorem levi_smooth (I : Set G.rootBase.support) : Algebra.Smooth K (G.leviAlgebra I) :=
  (smoothCommHopfAlgProperty_iff (CommHopfAlgCat.of K (G.leviAlgebra I))).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _)

/-- The reduced Levi--Borel coordinate algebra is smooth over the base field. -/
theorem leviBorel_smooth (I : Set G.rootBase.support) :
    Algebra.Smooth K (G.leviBorelAlgebra I) :=
  (smoothCommHopfAlgProperty_iff (CommHopfAlgCat.of K (G.leviBorelAlgebra I))).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _)

/-- The Levi--Borel ideal contains the Levi ideal. -/
theorem leviIdeal_le_leviBorel (I : Set G.rootBase.support) :
    G.leviIdeal I ≤ G.leviBorelIdeal I := by
  apply (HopfIdeal.le_vanishingIdeal_iff (G.leviBorelPoints I) (G.leviIdeal I)).mpr
  rw [G.leviIdeal_points]
  exact inf_le_left

/-- The Levi--Borel ideal contains the Borel ideal. -/
theorem borelIdeal_le_leviBorel (I : Set G.rootBase.support) :
    G.borelIdeal ≤ G.leviBorelIdeal I :=
  (HopfIdeal.le_vanishingIdeal_iff (G.leviBorelPoints I) G.borelIdeal).mpr inf_le_right

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced :
    IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
      G.torusIdeal) := by
  change IsReduced G.torusAlgebra
  let : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra
attribute [local instance] torusReduced

/-- The torus ideal contains the Levi--Borel ideal. -/
theorem leviBorelIdeal_le_torus (I : Set G.rootBase.support) :
    G.leviBorelIdeal I ≤ G.torusIdeal := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  exact (G.torus_le_leviBorelPoints I).trans_eq (G.leviBorelIdeal_points I).symm

end ReductiveGroups.ReductiveGroupData
