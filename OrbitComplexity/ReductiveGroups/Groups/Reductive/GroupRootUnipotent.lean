import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSupport
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-! # Smooth connected unipotence of closed root groups

The closed positive-root groups are reduced polynomial groups inside the Borel's
unipotent group. Smoothness and unipotence pass to these closed subgroups.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Every closed positive-root group is smooth unipotent. -/
theorem rootSubset_smoothUnipotent (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    smoothUnipotentCommHopfAlgProperty K (G.rootSubsetAlgebra R hR) := by
  let f : G.unipotentAlgebra ⟶ G.rootSubsetAlgebra R hR :=
    FiniteTypeCommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra
      (G.unipotentIdeal_le_rootSubset R hR)
  have hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f) :=
    FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective G.coordinateAlgebra _
  have hs : Algebra.Smooth K (G.rootSubsetAlgebra R hR) :=
    (smoothCommHopfAlgProperty_iff (G.rootSubsetAlgebra R hR).obj).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _)
  exact smoothUnipotentCommHopfAlgProperty_of_surjective K f hf
    G.unipotent_geometricallyUnipotent hs

/-- Every closed positive-root group is geometrically connected. -/
theorem rootSubset_geometricallyConnected (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    geometricallyConnectedCommHopfAlgProperty K (G.rootSubsetAlgebra R hR).obj := by
  apply (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace K _).mpr
  infer_instance

end ReductiveGroups.ReductiveGroupData
