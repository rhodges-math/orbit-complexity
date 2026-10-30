import OrbitComplexity.GroupActions.Actions.FromPoints
import OrbitComplexity.GroupActions.Tori.Coordinates
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import OrbitComplexity.GroupActions.Varieties.AffineProduct

/-! # Weighted torus actions on affine space

A finite collection of lattice characters defines a diagonal action on affine space.
The coordinate morphism sends each variable to its character tensored with that variable.
The resulting algebraic action has the prescribed character formula on rational points.

## Main definitions

* GroupActions.torusWeightCharacter: multiplicative evaluation of a lattice character.
* GroupActions.weightedAffineAction: the diagonal algebraic action for a family of weights.

## Main results

* GroupActions.weightedAffineAction_smul: the coordinate formula for the diagonal action.
* GroupActions.weightedAffineAction_ne_zero: preservation of nonzero coordinates.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace GroupActions
variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

private theorem torusReducedWeighted : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra
attribute [local instance] torusReducedWeighted

private def torusBialgEquiv : G.torusAlgebra ≃ₐc[K]
    MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) := by
  let f : G.torusAlgebra →ₐc[K]
      MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) :=
    Bialgebra.Quotient.liftBialgHom G.torusIdeal.toIdeal G.torusSplit
      (fun a ha => (G.split_eq_zero a).mpr ha)
  have hf : ∀ a, f a = 0 ↔ a = 0 := by
    intro a
    induction a using Quotient.inductionOn' with
    | h a =>
      change G.torusSplit a = 0 ↔ Ideal.Quotient.mk G.torusIdeal.toIdeal a = 0
      rw [G.split_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact BialgEquiv.ofBijective f ⟨by
    intro a b h
    apply sub_eq_zero.mp
    apply (hf _).mp
    rw [map_sub, h, sub_self], by
    intro y
    obtain ⟨a, ha⟩ := G.split_surjective y
    exact ⟨Ideal.Quotient.mk G.torusIdeal.toIdeal a, ha⟩⟩

private theorem torusBialgEquiv_eq :
    (torusBialgEquiv G).toAlgEquiv = torusCoordinateEquiv G := by
  ext a
  induction a using Quotient.inductionOn' with
  | h a => rfl

private theorem weightGroupLike (w : G.torusIndex →₀ ℤ) :
    IsGroupLikeElem K ((torusCoordinateEquiv G).symm
      (MonoidAlgebra.single (Multiplicative.ofAdd w) 1)) := by
  rw [← torusBialgEquiv_eq]
  exact (MonoidAlgebra.isGroupLikeElem_single_one _).map (torusBialgEquiv G).symm

/-- Evaluation of a lattice character is multiplicative on torus rational points. -/
def torusWeightCharacter (w : G.torusIndex →₀ ℤ) : (torusVariety G).points →* K where
  toFun t := affinePointsEquiv.symm t
    ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (Multiplicative.ofAdd w) 1))
  map_one' := by
    let q : (torusVariety G).points ≃* WithConv (G.torusAlgebra →ₐ[K] K) :=
      (affineGroupPointsMulEquiv K G.torusAlgebra).symm
    change q 1 _ = 1
    rw [map_one, AlgHom.convOne_apply, (weightGroupLike G w).counit_eq_one]
    rfl
  map_mul' t s := by
    let q : (torusVariety G).points ≃* WithConv (G.torusAlgebra →ₐ[K] K) :=
      (affineGroupPointsMulEquiv K G.torusAlgebra).symm
    change q (t * s) _ = q t _ * q s _
    rw [map_mul, AlgHom.convMul_apply, (weightGroupLike G w).comul_eq_tmul_self]
    rfl

variable {κ : Type u} [Finite κ]

@[instance_reducible]
private def tupleAction (w : κ → G.torusIndex →₀ ℤ) :
    MulAction (torusVariety G).points (κ → K) where
  smul t x i := x i * torusWeightCharacter G (w i) t
  one_smul x := by
    ext i
    change x i * torusWeightCharacter G (w i) 1 = x i
    rw [map_one, mul_one]
  mul_smul t s x := by
    ext i
    change x i * torusWeightCharacter G (w i) (t * s) =
      x i * torusWeightCharacter G (w i) s * torusWeightCharacter G (w i) t
    rw [map_mul]
    ring

@[instance_reducible]
private def pointAction (w : κ → G.torusIndex →₀ ℤ) :
    MulAction (torusVariety G).points (affineSpaceVariety K κ).points := by
  letI := tupleAction G w
  exact (affineSpaceVarietyPointsEquiv K κ).mulAction (torusVariety G).points

private def weightedActionMap (w : κ → G.torusIndex →₀ ℤ) :
    MvPolynomial κ K →ₐ[K] G.torusAlgebra ⊗[K] MvPolynomial κ K :=
  MvPolynomial.aeval (fun i =>
    (torusCoordinateEquiv G).symm (MonoidAlgebra.single (Multiplicative.ofAdd (w i)) 1)
      ⊗ₜ[K] MvPolynomial.X i)

private def weightedActionMorphism (w : κ → G.torusIndex →₀ ℤ) :
    (torusVariety G).toOver ⊗ (affineSpaceVariety K κ).toOver ⟶
      (affineSpaceVariety K κ).toOver :=
  Over.homMk ((pullbackSpecIso K G.torusAlgebra (MvPolynomial κ K)).hom ≫
    Spec.map (CommRingCat.ofHom (weightedActionMap G w).toRingHom)) (by
      change (pullbackSpecIso K G.torusAlgebra (MvPolynomial κ K)).hom ≫
        Spec.map (CommRingCat.ofHom (weightedActionMap G w).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial κ K))) = _
      rw [← Spec.map_comp]
      have h : CommRingCat.ofHom (algebraMap K (MvPolynomial κ K)) ≫
          CommRingCat.ofHom (weightedActionMap G w).toRingHom =
            CommRingCat.ofHom (algebraMap K
              (G.torusAlgebra ⊗[K] MvPolynomial κ K)) := by
        ext k
        exact (weightedActionMap G w).commutes k
      rw [h, pullbackSpecIso_hom_base]
      rfl)

private theorem weightedAction_pair (w : κ → G.torusIndex →₀ ℤ)
    (t : (torusVariety G).points) (x : (affineSpaceVariety K κ).points) :
    letI := pointAction G w
    lift ((torusVariety G).pointsEquivOverHom t)
        ((affineSpaceVariety K κ).pointsEquivOverHom x) ≫ weightedActionMorphism G w =
      (affineSpaceVariety K κ).pointsEquivOverHom (t • x) := by
  let := pointAction G w
  apply Over.OverMorphism.ext
  let t' : { p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of G.torusAlgebra) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K G.torusAlgebra)) = 𝟙 _ } := t
  let x' : { p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (MvPolynomial κ K)) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial κ K))) = 𝟙 _ } := x
  let p := (affinePointsEquiv.symm t', affinePointsEquiv.symm x')
  have hp := affineProductPointsEquiv_pullback K G.torusAlgebra (MvPolynomial κ K)
    (affinePointsEquiv ((tensorAlgebraPointsEquiv K G.torusAlgebra
      (MvPolynomial κ K)).symm p))
  simp only [affineProductPointsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Equiv.prodCongr_apply, Prod.map, p] at hp
  change CategoryTheory.Limits.pullback.lift t'.val x'.val
      (by exact t'.property.trans x'.property.symm) ≫
    (pullbackSpecIso K G.torusAlgebra (MvPolynomial κ K)).hom ≫
      Spec.map (CommRingCat.ofHom (weightedActionMap G w).toRingHom) = _
  rw [← hp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [affinePointsEquiv_apply, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((tensorAlgebraPointsEquiv K G.torusAlgebra (MvPolynomial κ K)).symm p).comp
      (weightedActionMap G w)).toRingHom) = _
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply congrArg (fun f : MvPolynomial κ K →ₐ[K] K => f.toRingHom)
  apply MvPolynomial.algHom_ext
  intro i
  change ((tensorAlgebraPointsEquiv K G.torusAlgebra (MvPolynomial κ K)).symm p)
      (weightedActionMap G w (MvPolynomial.X i)) =
    MvPolynomial.aeval (fun j => affineSpaceVarietyPointsEquiv K κ x j *
      torusWeightCharacter G (w j) t) (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X]
  simp only [weightedActionMap, MvPolynomial.aeval_X,
    tensorAlgebraPointsEquiv_symm_tmul]
  change torusWeightCharacter G (w i) t * affineSpaceVarietyPointsEquiv K κ x i = _
  exact mul_comm _ _

private theorem weightCharacter_ne_zero (w : G.torusIndex →₀ ℤ)
    (t : (torusVariety G).points) : torusWeightCharacter G w t ≠ 0 := by
  intro ht
  have h : torusWeightCharacter G w t * torusWeightCharacter G w t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [ht, zero_mul] at h
  exact zero_ne_one h

variable [IsAlgClosed K]

/-- Lattice weights define the diagonal algebraic torus action on affine space. -/
@[instance_reducible]
def weightedAffineAction (w : κ → G.torusIndex →₀ ℤ) :
    ModObj (torusVariety G).toOver (affineSpaceVariety K κ).toOver := by
  letI := pointAction G w
  exact Variety.modObjOfPoints _ _ (weightedActionMorphism G w) (weightedAction_pair G w)

/-- Each coordinate scales by the value of its prescribed lattice character. -/
theorem weightedAffineAction_smul (w : κ → G.torusIndex →₀ ℤ)
    (t : (torusVariety G).points) (x : (affineSpaceVariety K κ).points) (i : κ) :
    letI := weightedAffineAction G w
    affineSpaceVarietyPointsEquiv K κ (t • x) i =
      affineSpaceVarietyPointsEquiv K κ x i * affinePointsEquiv.symm t
        ((torusCoordinateEquiv G).symm
          (MonoidAlgebra.single (Multiplicative.ofAdd (w i)) 1)) := by
  let := weightedAffineAction G w
  let y := (affineSpaceVarietyPointsEquiv K κ).symm
    (fun j => affineSpaceVarietyPointsEquiv K κ x j * torusWeightCharacter G (w j) t)
  have hpair : lift ((torusVariety G).pointsEquivOverHom t)
      ((affineSpaceVariety K κ).pointsEquivOverHom x) ≫ weightedActionMorphism G w =
        (affineSpaceVariety K κ).pointsEquivOverHom y := weightedAction_pair G w t x
  have hpoint : t • x = y := by
    apply (affineSpaceVariety K κ).pointsEquivOverHom.injective
    rw [Variety.pointsEquivOverHom_smul]
    exact hpair
  rw [hpoint]
  change affineSpaceVarietyPointsEquiv K κ
    ((affineSpaceVarietyPointsEquiv K κ).symm _) i = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The diagonal torus action preserves the nonvanishing of each coordinate. -/
theorem weightedAffineAction_ne_zero (w : κ → G.torusIndex →₀ ℤ)
    (t : (torusVariety G).points) (x : (affineSpaceVariety K κ).points) (i : κ) :
    letI := weightedAffineAction G w
    affineSpaceVarietyPointsEquiv K κ (t • x) i ≠ 0 ↔
      affineSpaceVarietyPointsEquiv K κ x i ≠ 0 := by
  let := weightedAffineAction G w
  rw [weightedAffineAction_smul]
  change affineSpaceVarietyPointsEquiv K κ x i * torusWeightCharacter G (w i) t ≠ 0 ↔ _
  rw [mul_ne_zero_iff]
  exact ⟨And.left, fun h => ⟨h, weightCharacter_ne_zero G (w i) t⟩⟩

end GroupActions
