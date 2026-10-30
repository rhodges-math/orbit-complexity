import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubsetGroup
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing

/-!
# Closed root-support Hopf ideals

The vanishing Hopf ideal of a root-support subgroup has exactly the prescribed
rational points. Logarithm coordinates supply its defining support equations.
-/

noncomputable section
namespace ReductiveGroups.BorelRootSubset
open TauCeti
universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

private abbrev Tangent (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

variable (I J : HopfIdeal K B) (hJI : J ≤ I)
  (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
  (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
  (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
  (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
  (e : Module.Basis (borelRootCharacterIndex J π) K (Tangent J π hπ))
  (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
  (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
  (S : Set (borelRootCharacterIndex J π)) (hS : IsBorelRootCharacterClosed J π S)

include hJI hI hker hB he hx hS

/-- The closed-root-support subgroup, viewed in the ambient reductive group. -/
def ambientSubgroup : Subgroup (WithConv (B →ₐ[K] K)) :=
  (borelRootSubsetSubgroup I J hJI hI hJ π hπ hker hB x e he hx S hS).map
    (borelRootUnipotentPoints J π hπ).subtype

/-- The radical Hopf ideal of functions vanishing on the closed-root-support subgroup. -/
def ideal : HopfIdeal K B :=
  HopfIdeal.vanishingIdeal (ambientSubgroup I J hJI hI hJ π hπ hker hB x e he hx S hS)

/-- The subgroup defined by the root-support ideal lies in the unipotent subgroup. -/
theorem unipotentIdeal_le :
    borelRootUnipotentHopfIdeal J π hπ ≤ ideal I J hJI hI hJ π hπ hker hB x e he hx S hS := by
  apply (HopfIdeal.le_vanishingIdeal_iff _ _).mpr
  intro g hg
  obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hg
  exact u.property

private theorem logarithm_mem_ideal (i : borelRootCharacterIndex J π) (hi : i ∉ S) :
    borelRootLogarithmCoordinate J hJ π hπ (e.coord i) ∈
      ideal I J hJI hI hJ π hπ hker hB x e he hx S hS := by
  apply (HopfIdeal.mem_vanishingIdeal _ _).mpr
  intro g
  obtain ⟨u, hu, hval⟩ := Subgroup.mem_map.mp g.property
  have heq : u.val = g.val := hval
  rw [← heq]
  exact (borelRootLogarithmCoordinate_eval J hJ π hπ (e.coord i) u).trans (hu i hi)

/-- The root-support Hopf ideal cuts out exactly the prescribed rational-point subgroup. -/
theorem points_ideal :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
        (ideal I J hJI hI hJ π hπ hker hB x e he hx S hS) (CommAlgCat.of K K) =
      ambientSubgroup I J hJI hI hJ π hπ hker hB x e he hx S hS := by
  apply le_antisymm
  · intro g hg
    have hgU : g ∈ borelRootUnipotentPoints J π hπ := by
      apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ g).mpr
      intro b hb
      exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ g).mp hg b
        (unipotentIdeal_le I J hJI hI hJ π hπ hker hB x e he hx S hS hb)
    let u : borelRootUnipotentPoints J π hπ := ⟨g, hgU⟩
    have hu : u ∈ borelRootSubsetSubgroup I J hJI hI hJ π hπ hker hB x e he hx S hS := by
      change u ∈ borelRootSubsetPoints J hJ π hπ e S
      intro i hi
      rw [← borelRootLogarithmCoordinate_eval J hJ π hπ (e.coord i) u]
      exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ g).mp hg _
        (logarithm_mem_ideal I J hJI hI hJ π hπ hker hB x e he hx S hS i hi)
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  · exact (HopfIdeal.le_vanishingIdeal_iff _ _).mp le_rfl

end ReductiveGroups.BorelRootSubset
