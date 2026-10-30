import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentOperator
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight

/-! # Lie and point actions of finite comodules -/

noncomputable section

namespace ReductiveGroups.Coroot

section

open TauCeti LieAlgebra Module
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K B V : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [AddCommGroup V] [Module K V] [Comodule K B V] {n : ℕ}

/-- A finite comodule differentiates to the matrix representation in its chosen basis. -/
def finiteComoduleLie (b : Basis (Fin n) K V) :
    Derivation K B (Bialgebra.CounitAlgebra K B K) →ₗ⁅K⁆ Module.End K V :=
  (Matrix.toLinAlgEquiv b).toAlgHom.toLieHom.comp
    (affineGroupMatrixDifferential n (Comodule.coordinateBialgHom (H := B) b))

private def tangentOperator
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K)) : Module.End K V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ
    (TensorProduct.map LinearMap.id (scalarTangentLinear d)) ∘ₗ
      Comodule.coact (R := K) (C := B) (M := V)

private theorem differential_entry (b : Basis (Fin n) K V)
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K)) (i j : Fin n) :
    affineGroupMatrixDifferential n (Comodule.coordinateBialgHom (H := B) b) d i j =
      scalarTangentLinear d (Comodule.coefficientMatrix (C := B) b i j) := by
  rw [affineGroupMatrixDifferential_apply, GeneralLinear.tangentMatrix_apply,
    algEquivSelf_derivationComp_apply]
  erw [Comodule.coordinateBialgHom_X]
  rfl

/-- The differentiated matrix action is contraction of the original comodule coaction. -/
private theorem finiteComoduleLie_eq (b : Basis (Fin n) K V)
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K)) :
    finiteComoduleLie b d = tangentOperator d := by
  apply b.ext
  intro j
  change Matrix.toLin b b
    (affineGroupMatrixDifferential n (Comodule.coordinateBialgHom (H := B) b) d)
      (b j) = _
  rw [Matrix.toLin_self]
  change _ = (TensorProduct.rid K V)
    (TensorProduct.map LinearMap.id (scalarTangentLinear d)
      (Comodule.coact (R := K) (C := B) (M := V) (b j)))
  rw [Comodule.coact_basis_eq_sum_coefficientMatrix]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul, differential_entry]

variable {M : Type*} [CommGroup M]

/-- Every algebraic torus character is differentiated with its full character value. -/
private theorem finiteComoduleLie_weight (b : Basis (Fin n) K V)
    (pi : B →ₐc[K] MonoidAlgebra K M)
    (h : Derivation K (MonoidAlgebra K M)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K))
    (chi : M) (v : V) (hv : v ∈ DiagonalizableGroup.weightSpace V pi.toCoalgHom chi) :
    finiteComoduleLie b (derivationCompLieHom (B := K) pi h) v =
      characterDifferential chi h • v := by
  have hd : scalarTangentLinear (derivationCompLieHom (B := K) pi h) =
      (scalarTangentLinear h).comp pi.toLinearMap := by
    apply LinearMap.ext
    intro a
    exact algEquivSelf_derivationComp_apply pi h a
  rw [finiteComoduleLie_eq]
  change (TensorProduct.rid K V)
    (TensorProduct.map LinearMap.id
      (scalarTangentLinear (derivationCompLieHom (B := K) pi h))
        (Comodule.coact (R := K) (C := B) (M := V) v)) = _
  rw [hd]
  have hmap : TensorProduct.map (LinearMap.id : V →ₗ[K] V)
      ((scalarTangentLinear h).comp pi.toLinearMap) =
        (TensorProduct.map LinearMap.id (scalarTangentLinear h)).comp
          (TensorProduct.map LinearMap.id pi.toLinearMap) := by
    ext x y
    rfl
  rw [hmap, LinearMap.comp_apply]
  rw [show TensorProduct.map LinearMap.id pi.toLinearMap
      (Comodule.coact (R := K) (C := B) (M := V) v) =
        v ⊗ₜ[K] MonoidAlgebra.single chi 1 from DiagonalizableGroup.mem_weightSpace.mp hv]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul]
  rfl

/-- The same weight equation uses the torus tangent inside the original group. -/
theorem finiteComoduleLie_weight_image (b : Basis (Fin n) K V)
    (pi : B →ₐc[K] MonoidAlgebra K M) (hpi : Function.Surjective pi)
    (chi : M) (h : diagonalizableTangentImage pi) (v : V)
    (hv : v ∈ DiagonalizableGroup.weightSpace V pi.toCoalgHom chi) :
    finiteComoduleLie b (h : Derivation K B (Bialgebra.CounitAlgebra K B K)) v =
      characterDifferentialOnImage pi hpi chi h • v := by
  let ht := (diagonalizableTangentEquivImage pi hpi).symm h
  have he : derivationCompLieHom (B := K) pi ht =
      (h : Derivation K B (Bialgebra.CounitAlgebra K B K)) :=
    congrArg Subtype.val ((diagonalizableTangentEquivImage pi hpi).apply_symm_apply h)
  have hw := finiteComoduleLie_weight b pi ht chi v hv
  rw [he] at hw
  exact hw

end

section

open TauCeti Module WithConv
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {K B : Type u} {V : Type v} [Field K] [CommRing B] [HopfAlgebra K B]
  [AddCommGroup V] [Module K V] [Comodule K B V] {n : ℕ}

/-- A group point acts on the original comodule through its coordinate matrix. -/
def finiteComodulePoints (b : Basis (Fin n) K V) :
    WithConv (B →ₐ[K] K) →* Module.End K V :=
  (Matrix.toLinAlgEquiv b).toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp
      ((GeneralLinear.pointsMulEquiv n).toMonoidHom.comp
        (AlgHom.mapDomain (Comodule.coordinateBialgHom (H := B) b))))

private def pointOperator (g : B →ₐ[K] K) : Module.End K V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ
    (TensorProduct.map LinearMap.id g.toLinearMap) ∘ₗ
      Comodule.coact (R := K) (C := B) (M := V)

private theorem pointMatrix_entry (b : Basis (Fin n) K V)
    (g : WithConv (B →ₐ[K] K)) (i j : Fin n) :
    (GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain (Comodule.coordinateBialgHom (H := B) b) g) :
        Matrix (Fin n) (Fin n) K) i j =
      g.ofConv (Comodule.coefficientMatrix (C := B) b i j) := by
  change (GeneralLinear.pointsMulEquiv n
    (toConv (g.ofConv.comp (Comodule.coordinateBialgHom (H := B) b).toAlgHom)) :
      Matrix (Fin n) (Fin n) K) i j = _
  rw [AlgHom.pointsMulEquiv_comp_coordinateBialgHom, Matrix.map_apply]

/-- The coordinate-matrix point action contracts the original coaction. -/
private theorem finiteComodulePoints_eq (b : Basis (Fin n) K V)
    (g : WithConv (B →ₐ[K] K)) :
    finiteComodulePoints b g = pointOperator g.ofConv := by
  apply b.ext
  intro j
  change Matrix.toLin b b
    (GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain (Comodule.coordinateBialgHom (H := B) b) g) :
        Matrix (Fin n) (Fin n) K) (b j) = _
  rw [Matrix.toLin_self]
  change _ = (TensorProduct.rid K V)
    (TensorProduct.map LinearMap.id g.ofConv.toLinearMap
      (Comodule.coact (R := K) (C := B) (M := V) (b j)))
  rw [Comodule.coact_basis_eq_sum_coefficientMatrix]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul, AlgHom.toLinearMap_apply, pointMatrix_entry]

/-- Every torus point acts by the full algebraic character on its weight space. -/
theorem finiteComodulePoints_weight {M : Type*} [CommGroup M]
    (b : Basis (Fin n) K V) (pi : B →ₐc[K] MonoidAlgebra K M)
    (z : WithConv (MonoidAlgebra K M →ₐ[K] K)) (chi : M) (v : V)
    (hv : v ∈ DiagonalizableGroup.weightSpace V pi.toCoalgHom chi) :
    finiteComodulePoints b (AlgHom.mapDomain pi z) v =
      z.ofConv (MonoidAlgebra.single chi 1) • v := by
  rw [finiteComodulePoints_eq]
  change (TensorProduct.rid K V)
    (TensorProduct.map LinearMap.id (z.ofConv.comp pi.toAlgHom).toLinearMap
      (Comodule.coact (R := K) (C := B) (M := V) v)) = _
  have hmap : TensorProduct.map (LinearMap.id : V →ₗ[K] V)
      (z.ofConv.comp pi.toAlgHom).toLinearMap =
        (TensorProduct.map LinearMap.id z.ofConv.toLinearMap).comp
          (TensorProduct.map LinearMap.id pi.toLinearMap) := by
    ext x y
    rfl
  rw [hmap, LinearMap.comp_apply]
  rw [show TensorProduct.map LinearMap.id pi.toLinearMap
      (Comodule.coact (R := K) (C := B) (M := V) v) =
        v ⊗ₜ[K] MonoidAlgebra.single chi 1 from DiagonalizableGroup.mem_weightSpace.mp hv]
  simp

variable [CharZero K]

/-- The additive tangent has nilpotent action in every finite group comodule. -/
theorem finiteComoduleLie_ga_nilpotent (b : Basis (Fin n) K V)
    (x : B →ₐc[K] SymmetricAlgebra K K) :
    IsNilpotent (finiteComoduleLie b (gaAffineGroupTangent x)) :=
  (gaAffineGroupTangent_matrix_nilpotent n x
    (Comodule.coordinateBialgHom (H := B) b)).map (Matrix.toLinAlgEquiv b).toAlgHom

/-- The additive point action is the exponential of its differential. -/
theorem finiteComodulePoints_ga (b : Basis (Fin n) K V)
    (x : B →ₐc[K] SymmetricAlgebra K K) (t : K) :
    finiteComodulePoints b (gaParameterPoint x t) =
      associativeExponential (K := K)
        (finiteComoduleLie b (t • gaAffineGroupTangent x)) := by
  let : Module ℚ (Matrix (Fin n) (Fin n) K) :=
    Module.compHom _ (algebraMap ℚ K)
  let : Module ℚ (Module.End K V) := Module.compHom _ (algebraMap ℚ K)
  let rho := Comodule.coordinateBialgHom (H := B) b
  let e := (Matrix.toLinAlgEquiv b).toAlgHom
  let X := affineGroupMatrixDifferential n rho (gaAffineGroupTangent x)
  change e (GeneralLinear.pointsMulEquiv n
    (AlgHom.mapDomain rho (gaAffineGroupPoints x (Multiplicative.ofAdd t))) :
      Matrix (Fin n) (Fin n) K) = _
  rw [GaAffineGroupPoints.matrix_eq_exponential]
  have hm : e (associativeExponential (K := K) (t • X)) =
      associativeExponential (K := K) (e (t • X)) :=
    IsNilpotent.map_exp
      ((gaAffineGroupTangent_matrix_nilpotent n x rho).smul t) e
  change e (associativeExponential (K := K) (t • X)) = _
  rw [hm]
  congr 1

end


end ReductiveGroups.Coroot
