import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.RootSubsetCoordinates
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateBasis
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSets

/-!
# Coordinate algebras of closed positive-root subgroups

A single choice of Borel root maps and tangent basis gives closed subgroups
for integrally closed positive-root sets. Their coordinate algebras are polynomial
algebras indexed by the positive roots in the specified support.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem basis_exists :
    ∃ (x : borelRootCharacterIndex G.borelIdeal G.torusSplit →
        G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
      (e : Module.Basis (borelRootCharacterIndex G.borelIdeal G.torusSplit) K
        G.unipotentTangent),
      (∀ i, (e i).val = gaAffineGroupTangent (x i)) ∧
      (∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace G.torusSplit i.val) ∧
      gaGeneratedHopfIdeal x = G.unipotentIdeal :=
  exists_borelRootCoordinateBasis G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- A simultaneous choice of additive root subgroups realizing a Borel tangent basis. -/
def borelRootMaps : borelRootCharacterIndex G.borelIdeal G.torusSplit →
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K := Classical.choose G.basis_exists

/-- The chosen basis of the unipotent tangent, indexed by Borel root characters. -/
def borelRootBasis : Module.Basis (borelRootCharacterIndex G.borelIdeal G.torusSplit) K
    G.unipotentTangent := Classical.choose (Classical.choose_spec G.basis_exists)

/-- The chosen basis vectors are the tangents of the chosen root subgroup maps. -/
theorem borelRootBasis_tangent (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    (G.borelRootBasis i).val = gaAffineGroupTangent (G.borelRootMaps i) :=
  (Classical.choose_spec (Classical.choose_spec G.basis_exists)).1 i

/-- Each chosen additive subgroup tangent has its indexing torus character. -/
theorem borelRootMaps_weight (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    gaAffineGroupTangent (G.borelRootMaps i) ∈
      affineGroupCharacterWeightSpace G.torusSplit i.val :=
  (Classical.choose_spec (Classical.choose_spec G.basis_exists)).2.1 i

/-- The Hopf ideal of the subgroup supported on a closed positive-root subset. -/
def rootSubsetIdeal (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R) :
    HopfIdeal K G.coordinateAlgebra :=
  BorelRootSubset.ideal G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
    G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps
    G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
    (G.rootCharacters R) (G.rootCharacters_closed R hR)

/-- The finite type coordinate Hopf algebra of a closed positive-root subgroup. -/
def rootSubsetAlgebra (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R) :
    FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra (G.rootSubsetIdeal R hR)

/-- Root-support coordinate indices correspond to the positive roots in the specified set. -/
def rootSubsetIndexEquiv (R : Set G.rootIndex) :
    G.rootCharacters R ≃ {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} :=
  (G.borelCharacterRootEquiv.subtypeEquiv (q := fun r => r.val ∈ R)
    (fun _ => Iff.rfl)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun r => G.rootBase.IsPos r) (fun r => r ∈ R))

/-- A fixed ordering of all coordinate roots in the specified support. -/
def rootSubsetOrder (R : Set G.rootIndex) : List (G.rootCharacters R) := by
  classical
  let _ := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let _ : Fintype (G.rootCharacters R) := Fintype.ofFinite _
  exact Finset.univ.toList

private theorem rootSubsetOrder_nodup (R : Set G.rootIndex) : (G.rootSubsetOrder R).Nodup := by
  classical
  simp only [rootSubsetOrder, Finset.nodup_toList]

private theorem rootSubsetOrder_complete (R : Set G.rootIndex) (i : G.rootCharacters R) :
    i ∈ G.rootSubsetOrder R := by
  classical
  simp only [rootSubsetOrder, Finset.mem_toList, Finset.mem_univ]

/-- Ordered additive root multiplication gives polynomial coordinates on a closed root subgroup. -/
def rootSubsetCoordinateEquiv (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    G.rootSubsetAlgebra R hR ≃ₐ[K]
      MvPolynomial {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} K :=
  (BorelRootSubset.coordinateEquiv G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
    G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps
    G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight (G.rootCharacters R)
    (G.rootCharacters_closed R hR) (G.rootSubsetOrder R) (G.rootSubsetOrder_nodup R)
    (G.rootSubsetOrder_complete R)).trans
      (MvPolynomial.renameEquiv K (G.rootSubsetIndexEquiv R))

/-- The root-subgroup chart sends each coordinate class to its ordered-product polynomial. -/
theorem rootSubsetCoordinateEquiv_mk (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (b : G.coordinateAlgebra) :
    G.rootSubsetCoordinateEquiv R hR (Ideal.Quotient.mk _ b) =
      MvPolynomial.rename (G.rootSubsetIndexEquiv R)
        (gaProductCoordinate (fun i : G.rootCharacters R => G.borelRootMaps i.val)
          (G.rootSubsetOrder R) b) := by
  rfl

/-- The coordinate algebra of a closed positive-root subgroup is a domain. -/
instance rootSubsetAlgebra_isDomain (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) : IsDomain (G.rootSubsetAlgebra R hR) :=
  (G.rootSubsetCoordinateEquiv R hR).injective.isDomain
    (G.rootSubsetCoordinateEquiv R hR).toRingHom

/-- The defining ideal of the full unipotent subgroup is contained in every root-support ideal. -/
theorem unipotentIdeal_le_rootSubset (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) : G.unipotentIdeal ≤ G.rootSubsetIdeal R hR :=
  BorelRootSubset.unipotentIdeal_le G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
    (G.rootCharacters R) (G.rootCharacters_closed R hR)

/-- The group of rational points of a closed positive-root subgroup. -/
def rootSubsetPoints (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R) :
    Subgroup G.points :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
    (G.rootSubsetIdeal R hR) (CommAlgCat.of K K)

/-- Every closed positive-root subgroup lies in the chosen unipotent subgroup. -/
theorem rootSubsetPoints_le_unipotent (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) : G.rootSubsetPoints R hR ≤ G.unipotentPoints :=
  CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ (G.unipotentIdeal_le_rootSubset R hR) _

/-- Rational points of a root-support subgroup are precisely the supported logarithm points. -/
theorem rootSubsetPoints_eq (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R) :
    G.rootSubsetPoints R hR =
      (borelRootSubsetSubgroup G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
        G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps
        G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight (G.rootCharacters R)
        (G.rootCharacters_closed R hR)).map G.unipotentPoints.subtype :=
  BorelRootSubset.points_ideal G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
    G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps
    G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
    (G.rootCharacters R) (G.rootCharacters_closed R hR)

end ReductiveGroups.ReductiveGroupData
