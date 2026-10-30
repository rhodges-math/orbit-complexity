import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCentralizer
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus
import OrbitComplexity.ReductiveGroups.Groups.Borel.LeviBorelCenter

/-!
# Standard Levi point groups

The common kernel of the selected simple characters defines the central
diagonalizable subgroup. Its centralizer contains the supported root groups.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem torus_comm (s t : G.torusPoints) : s * t = t * s := by
  have hco : Coalgebra.IsCocomm K (CommHopfAlgCat.quotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal) :=
    G.torus_isTorus.isCocomm K G.torusAlgebra
  have hcomm : IsMulCommutative G.torusPoints :=
    @CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup K _
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal hco (CommAlgCat.of K K)
  exact @mul_comm' G.torusPoints _ hcomm s t

/-- The torus points on which all selected simple root characters take the value one. -/
def leviCenterPoints (I : Set G.rootBase.support) : Set G.points :=
  ReductiveGroups.leviCenterPoints G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive I

/-- The standard Levi point group centralizes the selected simple-character common kernel. -/
def leviPoints (I : Set G.rootBase.support) : Subgroup G.points :=
  Subgroup.centralizer (G.leviCenterPoints I)

/-- The standard Levi--Borel point group is the intersection of Levi and Borel point groups. -/
def leviBorelPoints (I : Set G.rootBase.support) : Subgroup G.points :=
  G.leviPoints I ⊓ G.borelPoints

/-- The selected Levi central points lie in the fixed maximal torus. -/
theorem leviCenterPoints_le_torus (I : Set G.rootBase.support) :
    G.leviCenterPoints I ⊆ G.torusPoints := by
  rintro g ⟨t, rfl, _⟩
  exact (ReductiveGroups.mem_torusPoints_iff G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero _).mpr ⟨t, rfl⟩

/-- The fixed maximal torus lies in every standard Levi point group. -/
theorem torus_le_leviPoints (I : Set G.rootBase.support) :
    G.torusPoints ≤ G.leviPoints I := by
  intro t ht
  change ∀ z ∈ G.leviCenterPoints I, z * t = t * z
  intro z hz
  exact congrArg Subtype.val (torus_comm G
    (⟨z, G.leviCenterPoints_le_torus I hz⟩ : G.torusPoints) ⟨t, ht⟩)

/-- The fixed maximal torus lies in every standard Levi--Borel point group. -/
theorem torus_le_leviBorelPoints (I : Set G.rootBase.support) :
    G.torusPoints ≤ G.leviBorelPoints I :=
  le_inf (G.torus_le_leviPoints I) G.torus_le_borel

/-- Every positive-root subgroup supported on the selected Levi roots centralizes the center. -/
theorem rootSubsetPoints_le_leviPoints (I : Set G.rootBase.support)
    (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R)
    (hsub : R ⊆ leviPositiveRoots G.rootBase I) :
    G.rootSubsetPoints R hR ≤ G.leviPoints I := by
  intro u hu
  change ∀ z ∈ G.leviCenterPoints I, z * u = u * z
  rintro _ ⟨z, rfl, hz⟩
  have hchar (i : G.rootCharacters R) :
      z.ofConv (MonoidAlgebra.single i.val.val 1) = 1 := by
    apply leviBorelRootSet_character_eq_one G.torusIdeal G.borelIdeal G.borel_le_torus
      G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero
      G.reductive I i.val ?_ z hz
    exact hsub i.property
  exact (mul_inv_eq_iff_eq_mul).mp (G.rootSubsetPoints_fixed R hR z hchar u hu)

/-- Every positive-root subgroup supported on the selected Levi roots lies in its Borel. -/
theorem rootSubsetPoints_le_leviBorel (I : Set G.rootBase.support)
    (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R)
    (hsub : R ⊆ leviPositiveRoots G.rootBase I) :
    G.rootSubsetPoints R hR ≤ G.leviBorelPoints I :=
  le_inf (G.rootSubsetPoints_le_leviPoints I R hR hsub)
    ((G.rootSubsetPoints_le_unipotent R hR).trans G.unipotent_le_borel)

end ReductiveGroups.ReductiveGroupData
