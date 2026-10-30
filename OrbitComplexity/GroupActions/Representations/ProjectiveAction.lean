import OrbitComplexity.GroupActions.Representations.ProjectiveMatrixFamily
import OrbitComplexity.GroupActions.Actions.FromPoints
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
import Mathlib.LinearAlgebra.Projectivization.Action
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Algebraic projective actions of finite comodules

The coefficient matrix of a comodule is invertible by the antipode identity. Its
projective matrix family realizes the point representation as an algebraic action.
Preserving a vector line is equivalent to fixing its associated projective point.
-/

noncomputable section
namespace GroupActions
open CategoryTheory AlgebraicGeometry TauCeti WithConv
open CartesianMonoidalCategory MonoidalCategory
open scoped Matrix
universe u v w x

section Lines
variable {K : Type u} {V : Type v} {ι : Type w}
  [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

omit [Fintype ι] in
private theorem projective_mk_fixed_iff (e : V ≃ₗ[K] V) (v : V) (hv : v ≠ 0) :
    Projectivization.mk K (e v) (e.map_ne_zero_iff.mpr hv) =
      Projectivization.mk K v hv ↔
        (Submodule.span K {v}).map e.toLinearMap = Submodule.span K {v} := by
  constructor
  · intro h
    have hs := congrArg Projectivization.submodule h
    simpa only [Projectivization.submodule_mk, Submodule.map_span,
      Set.image_singleton, LinearEquiv.coe_toLinearMap] using hs
  · intro h
    apply Projectivization.submodule_injective
    simpa only [Projectivization.submodule_mk, Submodule.map_span,
      Set.image_singleton, LinearEquiv.coe_toLinearMap] using h

private theorem basis_line_fixed_iff (b : Module.Basis ι K V) (e : V ≃ₗ[K] V)
    (v : V) (hv : v ≠ 0) :
    Projectivization.mk K (b.equivFun (e v))
        (b.equivFun.map_ne_zero_iff.mpr (e.map_ne_zero_iff.mpr hv)) =
      Projectivization.mk K (b.equivFun v)
        (b.equivFun.map_ne_zero_iff.mpr hv) ↔
      (Submodule.span K {v}).map e.toLinearMap = Submodule.span K {v} := by
  have hclass := (Projectivization.map_injective b.equivFun.toLinearMap
    b.equivFun.injective).eq_iff (a := Projectivization.mk K (e v)
      (e.map_ne_zero_iff.mpr hv)) (b := Projectivization.mk K v hv)
  simpa only [Projectivization.map_mk, LinearEquiv.coe_toLinearMap] using
    hclass.trans (projective_mk_fixed_iff e v hv)

end Lines

section Coefficients
variable {K : Type u} {H : Type v} {V : Type w} {ι : Type x}
  [Field K] [CommRing H] [HopfAlgebra K H]
  [AddCommGroup V] [Module K V] [Comodule K H V]
  [Fintype ι] [DecidableEq ι]

private def coefficientUnit (b : Module.Basis ι K V) : Matrix.GeneralLinearGroup ι H where
  val := Comodule.coefficientMatrix (C := H) b
  inv := (Comodule.coefficientMatrix (C := H) b).map (HopfAlgebra.antipode K)
  val_inv := Comodule.coefficientMatrix_mul_map_antipode b
  inv_val := Comodule.map_antipode_mul_coefficientMatrix b

private theorem coefficient_eval (b : Module.Basis ι K V) (g : WithConv (H →ₐ[K] K)) (i j : ι) :
    g.ofConv (coefficientUnit (H := H) b i j) =
      b.coord i (Comodule.basePointsRepresentation (H := H) V g (b j)) := by
  change g.ofConv (Comodule.coefficientMatrix (C := H) b i j) = _
  rw [Comodule.coefficientMatrix_apply, Comodule.apply_matrixCoefficient]

private def coordinateRepresentation (b : Module.Basis ι K V) :
    Representation K (WithConv (H →ₐ[K] K)) (ι → K) :=
  (b.equivFun.conjAlgEquiv K).toMonoidHom.comp
    (Comodule.basePointsRepresentation (H := H) V)

private theorem coordinate_action (b : Module.Basis ι K V) (g : WithConv (H →ₐ[K] K))
    (v : ι → K) :
    coordinateRepresentation b g v =
      ((coefficientUnit (H := H) b : Matrix ι ι H).map g.ofConv) *ᵥ v := by
  have hm : LinearMap.toMatrix b b (Comodule.basePointsRepresentation (H := H) V g) =
      (coefficientUnit (H := H) b : Matrix ι ι H).map g.ofConv := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    exact (coefficient_eval b g i j).symm
  have hr : (b.repr (b.equivFun.symm v) : ι → K) = v :=
    b.equivFun.apply_symm_apply v
  change (b.repr (Comodule.basePointsRepresentation (H := H) V g
    (b.equivFun.symm v)) : ι → K) = _
  rw [← LinearMap.toMatrix_mulVec_repr b b, hm, hr]

end Coefficients

section Action
variable {K H ι : Type u} {V : Type v} [Field K] [CommRing H] [HopfAlgebra K H]
  [IsReduced H] [Algebra.FiniteType K H]
  [AddCommGroup V] [Module K V] [Comodule K H V]
  [Fintype ι] [DecidableEq ι]

@[instance_reducible]
private def classAction (b : Module.Basis ι K V) :
    MulAction (affineVariety K H).points (Projectivization K (ι → K)) where
  smul g p := (coordinateRepresentation (H := H) b).asGroupHom
    ((affineGroupPointsMulEquiv K H).symm g) • p
  one_smul p := by
    change (coordinateRepresentation (H := H) b).asGroupHom
      ((affineGroupPointsMulEquiv K H).symm 1) • p = p
    rw [map_one, map_one, one_smul]
  mul_smul g h p := by
    change (coordinateRepresentation (H := H) b).asGroupHom
        ((affineGroupPointsMulEquiv K H).symm (g * h)) • p =
      (coordinateRepresentation (H := H) b).asGroupHom
        ((affineGroupPointsMulEquiv K H).symm g) •
      ((coordinateRepresentation (H := H) b).asGroupHom
        ((affineGroupPointsMulEquiv K H).symm h) • p)
    rw [map_mul, map_mul, mul_smul]

@[instance_reducible]
private def pointAction (b : Module.Basis ι K V) :
    MulAction (affineVariety K H).points (projectiveVariety K ι).points := by
  letI := classAction (H := H) b
  exact (projectivePointsEquiv (K := K) (ι := ι)).symm.mulAction (affineVariety K H).points

/-- A finite comodule defines a regular projective action morphism in a chosen basis. -/
def comoduleProjectiveMorphism (b : Module.Basis ι K V) :
    (affineVariety K H).toOver ⊗ (projectiveVariety K ι).toOver ⟶
      (projectiveVariety K ι).toOver :=
  projectiveMatrixFamily (coefficientUnit (H := H) b)

private theorem pair_vector [IsAlgClosed K] (b : Module.Basis ι K V)
    (g : WithConv (H →ₐ[K] K)) (v : ι → K) (hv : v ≠ 0) :
    letI := pointAction (H := H) b
    lift ((affineVariety K H).pointsEquivOverHom (affineGroupPointsMulEquiv K H g))
        ((projectiveVariety K ι).pointsEquivOverHom
          (projectivePointsEquiv (Projectivization.mk K v hv))) ≫
      comoduleProjectiveMorphism b =
        (projectiveVariety K ι).pointsEquivOverHom
          (affineGroupPointsMulEquiv K H g •
            projectivePointsEquiv (Projectivization.mk K v hv)) := by
  let := pointAction (H := H) b
  let a := Matrix.GeneralLinearGroup.map g.ofConv.toRingHom (coefficientUnit (H := H) b)
  have hn : (a : Matrix ι ι K) *ᵥ v ≠ 0 := by
    simpa only [Matrix.mulVec_zero] using (Matrix.mulVec_injective_of_isUnit a.isUnit).ne hv
  have hy : affineGroupPointsMulEquiv K H g •
        projectivePointsEquiv (Projectivization.mk K v hv) =
      projectivePointsEquiv (Projectivization.mk K ((a : Matrix ι ι K) *ᵥ v) hn) := by
    change projectivePointsEquiv
      ((coordinateRepresentation (H := H) b).asGroupHom
        ((affineGroupPointsMulEquiv K H).symm (affineGroupPointsMulEquiv K H g)) •
        (projectivePointsEquiv.symm
          (projectivePointsEquiv (Projectivization.mk K v hv)))) = _
    rw [MulEquiv.symm_apply_apply, Equiv.symm_apply_apply, Projectivization.smul_mk]
    change projectivePointsEquiv
      (Projectivization.mk K (coordinateRepresentation (H := H) b g v) _) = _
    congr 2
    exact coordinate_action b g v
  change lift ((affineVariety K H).pointsEquivOverHom (affinePointsEquiv g.ofConv))
      ((projectiveVariety K ι).pointsEquivOverHom (projectiveVectorPoint v hv)) ≫
      projectiveMatrixFamily (coefficientUnit (H := H) b) = _
  rw [projectiveMatrixFamily_points, hy, projectivePointsEquiv_mk]
  exact congrArg (projectiveVariety K ι).pointsEquivOverHom (projectiveMatrixMorphism_points a v hv)

variable [IsAlgClosed K]

/-- The comodule representation defines an algebraic group action on projective space. -/
@[instance_reducible]
def comoduleProjectiveAction (b : Module.Basis ι K V) :
    ModObj (affineVariety K H).toOver (projectiveVariety K ι).toOver := by
  letI := pointAction (H := H) b
  apply Variety.modObjOfPoints (affineVariety K H) (projectiveVariety K ι)
    (comoduleProjectiveMorphism b)
  intro g p
  obtain ⟨h, rfl⟩ := (affineGroupPointsMulEquiv K H).surjective g
  obtain ⟨q, rfl⟩ := (projectivePointsEquiv (K := K) (ι := ι)).surjective p
  induction q using Projectivization.ind with
  | h v hv => exact pair_vector b h v hv

/-- A nonzero vector defines a rational projective point through its basis coordinates. -/
def comoduleProjectivePoint (b : Module.Basis ι K V) (v : V) (hv : v ≠ 0) :
    (projectiveVariety K ι).points :=
  projectivePointsEquiv (Projectivization.mk K (b.equivFun v)
    (b.equivFun.map_ne_zero_iff.mpr hv))

/-- The projective action agrees with the comodule representation on vector classes. -/
theorem comoduleProjective_smul (b : Module.Basis ι K V)
    (g : WithConv (H →ₐ[K] K)) (v : V) (hv : v ≠ 0) :
    letI := comoduleProjectiveAction (H := H) b
    affineGroupPointsMulEquiv K H g • comoduleProjectivePoint b v hv =
      comoduleProjectivePoint b (Comodule.basePointsRepresentation (R := K) (H := H) V g v)
        ((LinearMap.GeneralLinearGroup.toLinearEquiv
          (Representation.asGroupHom
            (Comodule.basePointsRepresentation (R := K) (H := H) V) g)).map_ne_zero_iff.mpr
          hv) := by
  let := comoduleProjectiveAction (H := H) b
  let y : (projectiveVariety K ι).points :=
    letI := pointAction (H := H) b
    affineGroupPointsMulEquiv K H g • comoduleProjectivePoint b v hv
  have hpair : lift ((affineVariety K H).pointsEquivOverHom (affineGroupPointsMulEquiv K H g))
      ((projectiveVariety K ι).pointsEquivOverHom (comoduleProjectivePoint b v hv)) ≫
        comoduleProjectiveMorphism b = (projectiveVariety K ι).pointsEquivOverHom y :=
    pair_vector b g (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)
  have hpoint : affineGroupPointsMulEquiv K H g • comoduleProjectivePoint b v hv = y := by
    apply (projectiveVariety K ι).pointsEquivOverHom.injective
    rw [Variety.pointsEquivOverHom_smul]
    exact hpair
  rw [hpoint]
  change projectivePointsEquiv
      ((coordinateRepresentation (H := H) b).asGroupHom
        ((affineGroupPointsMulEquiv K H).symm (affineGroupPointsMulEquiv K H g)) •
        (projectivePointsEquiv.symm (projectivePointsEquiv (Projectivization.mk K
          (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv))))) = _
  rw [MulEquiv.symm_apply_apply, Equiv.symm_apply_apply, Projectivization.smul_mk]
  change projectivePointsEquiv (Projectivization.mk K
    (b.equivFun (Comodule.basePointsRepresentation (R := K) (H := H) V g
      (b.equivFun.symm (b.equivFun v))))
      _) = _
  unfold comoduleProjectivePoint
  apply congrArg (projectivePointsEquiv (K := K) (ι := ι))
  apply Projectivization.submodule_injective
  simp only [Projectivization.submodule_mk, LinearEquiv.symm_apply_apply]

/-- Fixing a projective vector point is equivalent to preserving its vector line. -/
theorem comoduleProjective_stabilizer (b : Module.Basis ι K V)
    (v : V) (hv : v ≠ 0) (g : WithConv (H →ₐ[K] K)) :
    letI := comoduleProjectiveAction (H := H) b
    affineGroupPointsMulEquiv K H g • comoduleProjectivePoint b v hv =
        comoduleProjectivePoint b v hv ↔
      (Submodule.span K {v}).map
          (Comodule.basePointsRepresentation (R := K) (H := H) V g) =
        Submodule.span K {v} := by
  let := comoduleProjectiveAction (H := H) b
  rw [comoduleProjective_smul]
  unfold comoduleProjectivePoint
  let e := (LinearMap.GeneralLinearGroup.toLinearEquiv
          (Representation.asGroupHom (Comodule.basePointsRepresentation (R := K) (H := H) V) g))
  have he := basis_line_fixed_iff b e v hv
  have hi := (projectivePointsEquiv (K := K) (ι := ι)).injective.eq_iff
    (a := Projectivization.mk K (b.equivFun (e v))
      (b.equivFun.map_ne_zero_iff.mpr (e.map_ne_zero_iff.mpr hv)))
    (b := Projectivization.mk K (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv))
  exact hi.trans he

section Weights

variable {M : Type u} [CommGroup M]

omit [IsReduced H] [Algebra.FiniteType K H] [IsAlgClosed K] in
private theorem point_weight (pi : H →ₐc[K] MonoidAlgebra K M)
    (z : WithConv (MonoidAlgebra K M →ₐ[K] K)) (chi : M) (v : V)
    (hv : v ∈ DiagonalizableGroup.weightSpace V pi.toCoalgHom chi) :
    Comodule.basePointsRepresentation (H := H) V (AlgHom.mapDomain pi z) v =
      z.ofConv (MonoidAlgebra.single chi 1) • v := by
  rw [Comodule.basePointsRepresentation_apply]
  change TensorProduct.lid K V
    (Comodule.endOfPoint V (z.ofConv.comp pi.toAlgHom) (1 ⊗ₜ[K] v)) = _
  rw [DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace V pi z.ofConv 1 hv]
  simp

omit [IsReduced H] [Algebra.FiniteType K H] [IsAlgClosed K] in
private theorem weight_coordinates (b : Module.Basis ι K V)
    (pi : H →ₐc[K] MonoidAlgebra K M) (chi : ι → M)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V pi.toCoalgHom (chi i))
    (z : WithConv (MonoidAlgebra K M →ₐ[K] K)) (v : V) :
    b.equivFun (Comodule.basePointsRepresentation (H := H) V
      (AlgHom.mapDomain pi z) v) =
        fun i => b.equivFun v i * z.ofConv (MonoidAlgebra.single (chi i) 1) := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  simp only [map_smul, point_weight pi z _ _ (hb _)]
  ext i
  simp [Module.Basis.equivFun_apply, Finsupp.single_apply, mul_comm]

/-- A weight basis gives the diagonal coordinate formula for the projective point action. -/
theorem comoduleProjective_weight_smul (b : Module.Basis ι K V)
    (pi : H →ₐc[K] MonoidAlgebra K M) (chi : ι → M)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V pi.toCoalgHom (chi i))
    (z : WithConv (MonoidAlgebra K M →ₐ[K] K)) (v : V) (hv : v ≠ 0) :
    letI := comoduleProjectiveAction (H := H) b
    affineGroupPointsMulEquiv K H (AlgHom.mapDomain pi z) •
        comoduleProjectivePoint b v hv =
      projectiveVectorPoint
        (fun i => b.equivFun v i * z.ofConv (MonoidAlgebra.single (chi i) 1))
        (by
          rw [← weight_coordinates b pi chi hb z v]
          exact b.equivFun.map_ne_zero_iff.mpr
            ((LinearMap.GeneralLinearGroup.toLinearEquiv
              (Representation.asGroupHom
                (Comodule.basePointsRepresentation (R := K) (H := H) V)
                (AlgHom.mapDomain pi z))).map_ne_zero_iff.mpr hv)) := by
  let := comoduleProjectiveAction (H := H) b
  have hcoords := weight_coordinates b pi chi hb z v
  simpa only [comoduleProjectivePoint, projectivePointsEquiv_mk, hcoords] using
    (@comoduleProjective_smul K H ι V inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance b (AlgHom.mapDomain pi z) v hv)

end Weights

end Action

end GroupActions
