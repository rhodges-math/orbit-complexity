import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTransport
import OrbitComplexity.ReductiveGroups.Groups.Hopf.ConjugateQuotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-!
# Defining ideals of transported root-support subgroups

Inclusion reverses the defining Hopf ideals, and a positive Weyl image is
the conjugate Hopf ideal. Reduced coordinate quotients make rational-point
identification detect equality of these closed subgroups.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Inclusion of root supports reverses inclusion of the defining Hopf ideals. -/
theorem rootSubsetIdeal_anti (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (hRS : R ⊆ S) : G.rootSubsetIdeal S hS ≤ G.rootSubsetIdeal R hR := by
  have h : G.rootSubsetIdeal R hR = HopfIdeal.vanishingIdeal (G.rootSubsetPoints R hR) := by
    rw [G.rootSubsetPoints_eq]
    rfl
  rw [h]
  exact (HopfIdeal.le_vanishingIdeal_iff _ _).mpr (G.rootSubsetPoints_mono R S hR hS hRS)

/-- A positive Weyl image gives the conjugate defining Hopf ideal of a closed root subgroup. -/
theorem rootSubsetIdeal_weyl_conj (w : G.weylGroup) (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (hposR : ∀ r ∈ R, G.rootBase.IsPos r) (hposS : ∀ s ∈ S, G.rootBase.IsPos s)
    (himage : S = G.rootSystem.weylGroupToPerm w '' R) :
    (G.rootSubsetIdeal R hR).conjugate (G.weylPoint w) = G.rootSubsetIdeal S hS := by
  let E := conjugateQuotientEquiv (G.rootSubsetIdeal R hR) (G.weylPoint w)
  let : IsDomain (G.coordinateAlgebra ⧸ (G.rootSubsetIdeal R hR).toIdeal) :=
    inferInstanceAs (IsDomain (G.rootSubsetAlgebra R hR))
  let : IsDomain (G.coordinateAlgebra ⧸
      ((G.rootSubsetIdeal R hR).conjugate (G.weylPoint w)).toIdeal) :=
    E.injective.isDomain E.toAlgEquiv.toRingHom
  let : IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
      ((G.rootSubsetIdeal R hR).conjugate (G.weylPoint w))) :=
    inferInstanceAs (IsReduced (G.coordinateAlgebra ⧸
      ((G.rootSubsetIdeal R hR).conjugate (G.weylPoint w)).toIdeal))
  let : IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.rootSubsetIdeal S hS)) := inferInstanceAs (IsReduced (G.rootSubsetAlgebra S hS))
  apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := K)
  rw [conjugatePoints_eq]
  change (G.rootSubsetPoints R hR).map (MulAut.conj (G.weylPoint w)).toMonoidHom =
    G.rootSubsetPoints S hS
  exact G.rootSubsetPoints_weyl_eq w R S hR hS hposR hposS himage

end ReductiveGroups.ReductiveGroupData
