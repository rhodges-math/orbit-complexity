import OrbitComplexity.GroupActions.Tori.SupportMaps
import OrbitComplexity.GroupActions.Representations.ProjectiveAction
import OrbitComplexity.GroupActions.Actions.Restriction
import OrbitComplexity.GroupActions.Actions.Orbits
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike

/-! # Weight coordinates for projective torus actions

A diagonal comodule acts by its evaluated characters. A weight basis of a reductive-group
comodule identifies the chosen torus orbits with these diagonal projective orbits, on the
same projective space and the same vector point.
-/

open CategoryTheory AlgebraicGeometry Multiplicative TauCeti WithConv
open scoped TensorProduct
noncomputable section
namespace GroupActions
universe u v

section Diagonal
variable {K I J : Type u} [Field K] [Fintype I] [DecidableEq I] [Finite J]

/-- The group algebra of a finite-rank free lattice is of finite type. -/
instance latticeAlgebra_finiteType :
    Algebra.FiniteType K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) :=
  MonoidAlgebra.finiteType_iff_group_fg.mpr
    (AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp inferInstance))

omit [Finite J] in
private theorem weights_basis (χ : I → J →₀ ℤ)
    (g : WithConv (MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K)) (i : I) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    Comodule.basePointsRepresentation (I → K) g ((Pi.basisFun K I) i) =
      g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) • (Pi.basisFun K I) i := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul]
  change TensorProduct.lid K (I → K) (1 • TensorProduct.comm K (I → K) K
    ((LinearMap.lTensor (I → K) g.ofConv.toLinearMap)
      ((Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))).coact
        ((Pi.basisFun K I) i)))) = _
  rw [Comodule.ofWeights_coact_basis]
  simp

omit [Finite J] in
private theorem weights_apply (χ : I → J →₀ ℤ)
    (g : WithConv (MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K))
    (v : I → K) (i : I) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    Comodule.basePointsRepresentation (I → K) g v i =
      v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  conv_lhs => rw [← (Pi.basisFun K I).sum_repr v]
  rw [map_sum]
  simp only [map_smul, weights_basis χ g]
  simp [Pi.basisFun_apply, Pi.single_apply, smul_eq_mul, mul_comm]

omit [Finite J] in
/-- A character evaluates to a nonzero scalar at every group-algebra point. -/
theorem projective_character_ne_zero
    (g : MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K) (m : J →₀ ℤ) :
    g (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 := by
  have h : g (MonoidAlgebra.single (ofAdd m) 1) *
      g (MonoidAlgebra.single (ofAdd (-m)) 1) = 1 := by
    rw [← map_mul, MonoidAlgebra.single_mul_single]
    simp [← MonoidAlgebra.one_def]
  exact left_ne_zero_of_mul_eq_one h

variable [IsAlgClosed K]

/-- A diagonal comodule acts on a projective vector by its evaluated characters. -/
theorem projective_weights_smul (χ : I → J →₀ ℤ)
    (g : WithConv (MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K))
    (v : I → K) (hv : v ≠ 0) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    affineGroupPointsMulEquiv K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) g •
        projectiveVectorPoint v hv =
      projectiveVectorPoint
        (fun i => v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1))
        (by
          intro hzero
          apply hv
          funext i
          exact (mul_eq_zero.mp (congrFun hzero i)).resolve_right
            (projective_character_ne_zero g.ofConv (χ i))) := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
  have heq : Comodule.basePointsRepresentation
      (H := MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) g v =
      (fun i => v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) :=
    funext (weights_apply χ g v)
  simpa only [comoduleProjectivePoint, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, projectivePointsEquiv_mk, heq] using
    (@comoduleProjective_smul K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I) g v hv)

end Diagonal

section Torus

variable {K I : Type u} {V : Type v} [Field K] [IsAlgClosed K]
  [Fintype I] [DecidableEq I] (G : ReductiveGroups.ReductiveGroupData K)
  [AddCommGroup V] [Module K V]
  [Comodule K G.coordinateAlgebra V]

private theorem torus_diagonal_smul (b : Module.Basis I K V)
    (chi : I → G.torusIndex →₀ ℤ)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom
      (ofAdd (chi i))) (v : V) (hv : v ≠ 0)
    (t : (torusVariety G).points)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K))
    (hz : (torusPointsMulEquiv G t : G.points) = AlgHom.mapDomain G.torusSplit z) :
    letI : ModObj (reductiveVariety G).toOver (projectiveVariety K I).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra I V
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    letI := Mod.scalarRestriction (torusInclusion G) (projectiveVariety K I).toOver
    letI : Comodule K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))
        (I → K) := Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (chi i))
    letI := comoduleProjectiveAction
      (H := MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) (Pi.basisFun K I)
    t • comoduleProjectivePoint b v hv =
      affineGroupPointsMulEquiv K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) z •
        comoduleProjectivePoint b v hv := by
  let : ModObj (reductiveVariety G).toOver (projectiveVariety K I).toOver :=
    @comoduleProjectiveAction K G.coordinateAlgebra I V
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  let := Mod.scalarRestriction (torusInclusion G) (projectiveVariety K I).toOver
  let : Comodule K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))
      (I → K) := Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (chi i))
  let := comoduleProjectiveAction
    (H := MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) (Pi.basisFun K I)
  rw [Variety.restricted_smul, torusInclusion_points, hz]
  have hleft := @comoduleProjective_weight_smul K G.coordinateAlgebra I V
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (Multiplicative (G.torusIndex →₀ ℤ)) inferInstance b G.torusSplit
    (fun i => ofAdd (chi i)) hb z v hv
  have hright := @projective_weights_smul K I G.torusIndex
    inferInstance inferInstance inferInstance inferInstance inferInstance
    chi z (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)
  exact hleft.trans hright.symm

/-- A weight basis identifies the chosen torus orbits with diagonal projective orbits. -/
theorem torus_projective_orbit (b : Module.Basis I K V)
    (chi : I → G.torusIndex →₀ ℤ)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom
      (ofAdd (chi i))) (v : V) (hv : v ≠ 0) :
    letI : ModObj (reductiveVariety G).toOver (projectiveVariety K I).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra I V
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    letI := Mod.scalarRestriction (torusInclusion G) (projectiveVariety K I).toOver
    MulAction.orbit (torusVariety G).points (comoduleProjectivePoint b v hv) =
      letI : Comodule K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))
          (I → K) := Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (chi i))
      letI := comoduleProjectiveAction
        (H := MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) (Pi.basisFun K I)
      MulAction.orbit
        (affineVariety K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))).points
        (comoduleProjectivePoint b v hv) := by
  let : ModObj (reductiveVariety G).toOver (projectiveVariety K I).toOver :=
    @comoduleProjectiveAction K G.coordinateAlgebra I V
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  let := Mod.scalarRestriction (torusInclusion G) (projectiveVariety K I).toOver
  let : Comodule K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))
      (I → K) := Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (chi i))
  let := comoduleProjectiveAction
    (H := MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) (Pi.basisFun K I)
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨z, hz⟩ := (ReductiveGroups.mem_torusPoints_iff G.torusIdeal G.torusSplit
      G.split_surjective G.split_eq_zero (torusPointsMulEquiv G t)).mp
        (torusPointsMulEquiv G t).property
    exact MulAction.mem_orbit_iff.mpr ⟨affineGroupPointsMulEquiv K _ z,
      (torus_diagonal_smul G b chi hb v hv t z hz).symm.trans ht⟩
  · intro hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨z, rfl⟩ := (affineGroupPointsMulEquiv K
      (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))).surjective g
    have hzmem : AlgHom.mapDomain G.torusSplit z ∈ G.torusPoints :=
      (ReductiveGroups.mem_torusPoints_iff G.torusIdeal G.torusSplit
        G.split_surjective G.split_eq_zero _).mpr ⟨z, rfl⟩
    let t := (torusPointsMulEquiv G).symm ⟨AlgHom.mapDomain G.torusSplit z, hzmem⟩
    have hz : (torusPointsMulEquiv G t : G.points) = AlgHom.mapDomain G.torusSplit z :=
      congrArg Subtype.val ((torusPointsMulEquiv G).apply_symm_apply _)
    exact MulAction.mem_orbit_iff.mpr
      ⟨t, (torus_diagonal_smul G b chi hb v hv t z hz).trans hg⟩

/-- The chosen torus and diagonal actions have equal scheme orbit closures in a weight basis. -/
theorem torus_projective_closure (b : Module.Basis I K V)
    (chi : I → G.torusIndex →₀ ℤ)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom
      (ofAdd (chi i))) (v : V) (hv : v ≠ 0) :
    letI : ModObj (reductiveVariety G).toOver (projectiveVariety K I).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra I V
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    letI := Mod.scalarRestriction (torusInclusion G) (projectiveVariety K I).toOver
    orbitClosure (torusVariety G) (projectiveVariety K I) (comoduleProjectivePoint b v hv) =
      letI : Comodule K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))
          (I → K) := Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (chi i))
      letI := comoduleProjectiveAction
        (H := MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) (Pi.basisFun K I)
      orbitClosure
        (affineVariety K (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))))
        (projectiveVariety K I) (comoduleProjectivePoint b v hv) := by
  let : ModObj (reductiveVariety G).toOver (projectiveVariety K I).toOver :=
    @comoduleProjectiveAction K G.coordinateAlgebra I V
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  let := Mod.scalarRestriction (torusInclusion G) (projectiveVariety K I).toOver
  unfold orbitClosure
  rw [torus_projective_orbit G b chi hb v hv]

end Torus

end GroupActions
