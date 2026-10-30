import OrbitComplexity.GroupActions.Representations.ExteriorActions
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositeTangent
import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
import TauCeti.LinearAlgebra.ExteriorPower
import Mathlib.LinearAlgebra.Projection
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositiveCharacter

/-!
# The positive-unipotent determinant coefficient

The exterior degree is the dimension of the positive-unipotent tangent,
not the dimension of the Borel. The torus determinant is the full positive-root
character; all torus tangent directions, including central directions, have weight zero.
-/

open ReductiveGroups TauCeti GroupActions
open scoped BigOperators TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The algebraic adjoint exterior representation in degree `dim Lie(U)`. -/
@[instance_reducible]
def adjointExteriorComodule :
    Comodule K G.coordinateAlgebra
      (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent) :=
  letI := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  exteriorPowerComodule (K := K) (H := G.coordinateAlgebra)
    (V := G.tangent) (Module.finrank K G.unipotentTangent)

private def oppositeComplement : Submodule K G.tangent :=
  G.borelTangent.toSubmodule.map
    (affineGroupAdjointLieEquiv G.longestPoint).toLinearEquiv.symm.toLinearMap

private theorem positive_isCompl :
    IsCompl G.unipotentTangent.toSubmodule (oppositeComplement G) := by
  let e := (affineGroupAdjointLieEquiv G.longestPoint).toLinearEquiv
  have hop : G.oppositeUnipotentTangent.toSubmodule =
      G.unipotentTangent.toSubmodule.map e.toLinearMap := by
    change (hopfTangentImage (G.unipotentIdeal.conjugate G.longestPoint)).toSubmodule = _
    rw [conjugate_tangentImage]
  have h := Submodule.isCompl_map e.symm G.oppositeUnipotent_isCompl_borel
  rw [hop, ← Submodule.map_comp] at h
  simpa only [e, oppositeComplement, LinearEquiv.symm_comp, Submodule.map_id] using h

private def positiveProjection : G.tangent →ₗ[K] G.unipotentTangent :=
  G.unipotentTangent.toSubmodule.projectionOnto (oppositeComplement G) (positive_isCompl G)

/-- The wedge of a basis of the positive-unipotent tangent, included in Lie(G). -/
def positiveDetVector : ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent :=
  exteriorPower.map (Module.finrank K G.unipotentTangent)
    G.unipotentTangent.toSubmodule.subtype
    (exteriorPower.ιMulti K (Module.finrank K G.unipotentTangent)
      (Module.finBasis K G.unipotentTangent))

/-- The determinant functional uses the opposite-Borel complement. -/
def positiveDetFunctional :
    (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent) →ₗ[K] K :=
  (exteriorPower.topEquiv (Module.finBasis K G.unipotentTangent)).toLinearMap.comp
    (exteriorPower.map (Module.finrank K G.unipotentTangent) (positiveProjection G))

/-- The determinant functional takes the chosen determinant vector to one. -/
theorem positiveDet_pairing : positiveDetFunctional G (positiveDetVector G) = 1 := by
  have hp : (positiveProjection G).comp G.unipotentTangent.toSubmodule.subtype =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact Submodule.projectionOnto_apply_left (positive_isCompl G) x
  change exteriorPower.topEquiv (Module.finBasis K G.unipotentTangent)
    (exteriorPower.map _ (positiveProjection G)
      (exteriorPower.map _ G.unipotentTangent.toSubmodule.subtype
        (exteriorPower.ιMulti K _ (Module.finBasis K G.unipotentTangent)))) = 1
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hp, exteriorPower.map_id,
    LinearMap.id_apply, exteriorPower.topEquiv_apply_ιMulti, Module.Basis.det_self]

/-- The constructed positive determinant vector is nonzero. -/
theorem positiveDet_ne_zero : positiveDetVector G ≠ 0 := by
  intro h
  have hh := positiveDet_pairing G
  rw [h, map_zero] at hh
  exact zero_ne_one hh

/-- A regular matrix coefficient of the full algebraic adjoint exterior representation. -/
def positiveDetCoefficient : G.coordinateAlgebra :=
  letI := adjointExteriorComodule G
  Comodule.matrixCoefficient (C := G.coordinateAlgebra)
    (positiveDetFunctional G) (positiveDetVector G)

/-- Evaluation at the identity normalizes the constructed regular coefficient to one. -/
theorem positiveDet_counit :
    Coalgebra.counit (R := K) (A := G.coordinateAlgebra) (positiveDetCoefficient G) = 1 := by
  let := adjointExteriorComodule G
  change Coalgebra.counit (R := K) (A := G.coordinateAlgebra)
    (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G)) = 1
  rw [Comodule.counit_matrixCoefficient, positiveDet_pairing]

@[instance_reducible]
private def rootFintype :
    Fintype (borelRootCharacterIndex G.borelIdeal G.torusSplit) := by
  letI := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  exact Fintype.ofFinite _

attribute [local instance] rootFintype

/-- The determinant uses the full torus-lattice character, retaining central directions. -/
theorem positiveCharacter_product :
    (∏ i : borelRootCharacterIndex G.borelIdeal G.torusSplit, i.val) =
      G.positiveRootCharacter := by
  classical
  let := Fintype.ofFinite G.rootIndex
  rw [ReductiveGroupData.positiveRootCharacter,
    Finset.prod_subtype (p := G.rootBase.IsPos)
      (Finset.univ.filter G.rootBase.IsPos) (by simp)
      (fun r : G.rootIndex ↦ G.rootCharacter r)]
  apply Fintype.prod_equiv G.borelCharacterRootEquiv
  intro i
  change i.val = (G.characterRootEquiv.symm
    (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i))).val
  simp only [Equiv.symm_apply_apply, borelRootCharacterOccurring]

/-- The positive-unipotent torus action in its root-coordinate basis. -/
def positiveTorusEnd (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    Module.End K G.unipotentTangent :=
  G.borelRootBasis.constr K fun i ↦
    z.ofConv (MonoidAlgebra.single i.val 1) • G.borelRootBasis i

/-- Including this endomorphism into Lie(G) gives the original adjoint action. -/
theorem positiveTorusEnd_subtype
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    G.unipotentTangent.toSubmodule.subtype.comp (positiveTorusEnd G z) =
      (affineGroupAdjointRepresentation (TauCeti.AlgHom.mapDomain G.torusSplit z)).comp
        G.unipotentTangent.toSubmodule.subtype := by
  apply G.borelRootBasis.ext
  intro i
  simp only [LinearMap.comp_apply, positiveTorusEnd, Module.Basis.constr_basis]
  change z.ofConv (MonoidAlgebra.single i.val 1) • (G.borelRootBasis i).val =
    affineGroupAdjointRepresentation (TauCeti.AlgHom.mapDomain G.torusSplit z)
      (G.borelRootBasis i).val
  simp only [G.borelRootBasis_tangent]
  exact (AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit i.val z _
    (G.borelRootMaps_weight i)).symm

/-- The torus adjoint endomorphism on Lie(U) has determinant delta, not a
character determined only after quotienting away the centre. -/
theorem positiveTorus_determinant
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    LinearMap.det (positiveTorusEnd G z) =
      z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) := by
  classical
  have hm : LinearMap.toMatrix G.borelRootBasis G.borelRootBasis (positiveTorusEnd G z) =
      Matrix.diagonal (fun i ↦ z.ofConv (MonoidAlgebra.single i.val 1)) := by
    ext i j
    calc
      _ = (G.borelRootBasis.repr (positiveTorusEnd G z (G.borelRootBasis j))) i :=
        LinearMap.toMatrix_apply G.borelRootBasis G.borelRootBasis _ i j
      _ = _ := by
        rw [Matrix.diagonal_apply]
        by_cases hij : i = j
        · subst j
          simp [positiveTorusEnd]
        · simp [positiveTorusEnd, hij]
  rw [← LinearMap.det_toMatrix G.borelRootBasis, hm, Matrix.det_diagonal,
    ← map_prod, MonoidAlgebra.prod_single, Finset.prod_const_one, positiveCharacter_product]

/-- Every torus tangent direction, including the central ones, has adjoint weight zero. -/
theorem torusTangent_fixed
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) (x : G.torusTangent) :
    affineGroupAdjointRepresentation (TauCeti.AlgHom.mapDomain G.torusSplit z)
      (x : G.tangent) = x := by
  have hx : (x : G.tangent) ∈ affineGroupCharacterWeightSpace G.torusSplit 1 := by
    rw [G.identityWeightSpace_eq_torus]
    exact x.property
  simpa only [← MonoidAlgebra.one_def, map_one, one_smul] using
    AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit 1 z (x : G.tangent) hx

end SchubertGeometry.DeterminantSection
