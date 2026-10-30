import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Points
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCoroots
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic

/-! # The determinant-one diagonal one-parameter subgroup in SL2 -/

noncomputable section
namespace ReductiveGroups.SimpleDiagonal
open TauCeti WithConv
universe u
variable (K : Type u) [Field K]

private def exponentLinear : (ULift.{u} (Fin 2) →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun i => if i.down = 0 then (1 : ℤ) else -1)

private def exponent : Multiplicative (ULift.{u} (Fin 2) →₀ ℤ) →* Multiplicative ℤ where
  toFun m := Multiplicative.ofAdd (exponentLinear m.toAdd)
  map_one' := by
    change Multiplicative.ofAdd (exponentLinear 0) = 1
    rw [map_zero]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (exponentLinear (a.toAdd + b.toAdd)) =
      Multiplicative.ofAdd (exponentLinear a.toAdd + exponentLinear b.toAdd)
    rw [map_add]

private theorem exponent_single (i : ULift.{u} (Fin 2)) (n : ℤ) :
    exponent (Multiplicative.ofAdd (Finsupp.single i n)) =
      Multiplicative.ofAdd (n * (if i.down = 0 then (1 : ℤ) else -1)) := by
  change Multiplicative.ofAdd (exponentLinear (Finsupp.single i n)) = _
  simp [exponentLinear]

private def glMap : GeneralLinear.coordinateHopfAlgebra K 2 →ₐc[K]
    MonoidAlgebra K (Multiplicative ℤ) :=
  (MonoidAlgebra.mapDomainBialgHom K exponent).comp
    (GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := 2)).hom

private theorem glMap_X (i j : Fin 2) :
    glMap K (GeneralLinear.coordinateHopfAlgebraAlgEquiv K 2
      (GeneralLinear.coordinateRingMap K 2 (MvPolynomial.X (i, j)))) =
      if i = j then MonoidAlgebra.single
        (Multiplicative.ofAdd (if i = 0 then (1 : ℤ) else -1)) 1 else 0 := by
  rw [glMap, BialgHom.comp_apply, GeneralLinear.diagonalTorusCoordinateMap_X]
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    rw [MonoidAlgebra.mapDomainBialgHom_single, exponent_single]
    simp only [one_mul]
  · simp only [ite_eq_right hij, map_zero]

private theorem glMap_det :
    glMap K (GeneralLinear.determinantGroupLike K 2) = 1 := by
  simp [GeneralLinear.determinantGroupLike_val, Matrix.det_fin_two,
    glMap_X, ← MonoidAlgebra.one_def]

/-- The coordinate morphism of the diagonal map with entries z and its inverse. -/
def coordinateMap : SpecialLinear.coordinateHopfAlgebra K 2 →ₐc[K]
    MonoidAlgebra K (Multiplicative ℤ) :=
  (CommHopfAlgCat.liftQuotient (SpecialLinear.definingHopfIdeal K 2)
    (CommHopfAlgCat.ofHom (glMap K))
    (SpecialLinear.definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one
      K 2 (CommHopfAlgCat.ofHom (glMap K)) (glMap_det K))).hom

private theorem coordinateMap_comp :
    (coordinateMap K).comp (SpecialLinear.coordinateMap K 2).hom = glMap K := by
  apply DFunLike.ext
  intro x
  exact CommHopfAlgCat.liftQuotient_mk (SpecialLinear.definingHopfIdeal K 2)
    (CommHopfAlgCat.ofHom (glMap K))
    (SpecialLinear.definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one
      K 2 (CommHopfAlgCat.ofHom (glMap K)) (glMap_det K)) x

private theorem tangent_value (m : Multiplicative ℤ) :
    (Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K (Multiplicative ℤ)) K)
      (Coroot.multiplicativeTangent (MonoidAlgebra.single m 1)) = (m.toAdd : K) := by
  change characterDifferential m (Coroot.multiplicativeTangent (K := K)) = _
  unfold Coroot.multiplicativeTangent
  rw [CharacterDifferential.of_additive_tangent]
  rfl

/-- The diagonal one-parameter subgroup has the standard diagonal tangent matrix. -/
theorem coordinateMap_differential :
    derivationComp (B := K) (coordinateMap K) (Coroot.multiplicativeTangent (K := K)) =
      (SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm
        (TauCeti.slFinTwoBasis K (2 : Fin 3)) := by
  apply (SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).injective
  simp only [LieEquiv.coe_coe, LieEquiv.apply_symm_apply]
  apply Subtype.ext
  change (SpecialLinear.tangentMatrix 2
    (derivationComp (B := K) (coordinateMap K) (Coroot.multiplicativeTangent (K := K))) :
      Matrix (Fin 2) (Fin 2) K) = _
  rw [SpecialLinear.tangentMatrix_apply_coe]
  change GeneralLinear.tangentMatrix 2
    (((derivationComp (B := K) (SpecialLinear.coordinateMap K 2).hom).comp
      (derivationComp (B := K) (coordinateMap K)))
        (Coroot.multiplicativeTangent (K := K))) = _
  rw [← derivationComp_comp, coordinateMap_comp]
  ext i j
  rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply]
  change (Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K (Multiplicative ℤ)) K)
    (Coroot.multiplicativeTangent (glMap K
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv K 2
        (GeneralLinear.coordinateRingMap K 2 (MvPolynomial.X (i, j)))))) =
      ((TauCeti.slFinTwoBasis K (2 : Fin 3) : LieAlgebra.SpecialLinear.sl (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) i j
  rw [glMap_X K i j]
  rw [TauCeti.slFinTwoBasis_two, LieAlgebra.SpecialLinear.val_singleSubSingle]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.reduceFinMk, ite_true, ite_false, Fin.zero_ne_one,
      (show (1 : Fin 2) ≠ 0 from by decide)]
  all_goals try rw [tangent_value]
  all_goals simp
  all_goals rfl


private theorem unit_value (u : Kˣ) (m : Multiplicative ℤ) :
    ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u)).ofConv
      (MonoidAlgebra.single m 1) = ((u ^ m.toAdd : Kˣ) : K) := by
  have h := congrArg (fun f : Multiplicative ℤ →* Kˣ => (f m : K))
    ((DiagonalizableGroup.pointsMulEquiv (R := K)).apply_symm_apply (zpowersHom Kˣ u))
  simpa only [DiagonalizableGroup.pointsMulEquiv_apply,
    DiagonalizableGroup.charOfPoint_apply_coe, zpowersHom_apply] using h

/-- Evaluation of the diagonal coordinate morphism gives the diagonal unit matrix. -/
theorem coordinateMap_point (u : Kˣ) :
    AlgHom.mapDomain (coordinateMap K)
      ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u)) =
        (SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm
          (Matrix.SpecialLinearGroup.diag2 (u : K) (Units.ne_zero u)) := by
  let z := (DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u)
  apply (SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  ext i j
  have hv := congrArg (fun a : Matrix.GeneralLinearGroup (Fin 2) K => a i j)
    (SpecialLinear.pointsMulEquiv_toGL (R := K) (A := K) 2
      (AlgHom.mapDomain (coordinateMap K) z))
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply] at hv
  change z.ofConv (((coordinateMap K).comp (SpecialLinear.coordinateMap K 2).hom)
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv K 2
        (GeneralLinear.coordinateRingMap K 2 (MvPolynomial.X (i, j))))) =
      (((SpecialLinear.pointsMulEquiv (R := K) (A := K) 2)
        (AlgHom.mapDomain (coordinateMap K) z) : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) i j at hv
  change (((SpecialLinear.pointsMulEquiv (R := K) (A := K) 2)
    (AlgHom.mapDomain (coordinateMap K) z) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) i j = _
  rw [coordinateMap_comp, glMap_X] at hv
  rw [← hv]
  change z.ofConv (if i = j then MonoidAlgebra.single
      (Multiplicative.ofAdd (if i = 0 then (1 : ℤ) else -1)) 1 else 0) =
        (Matrix.SpecialLinearGroup.diag2 (u : K) (Units.ne_zero u)).val i j
  rw [Matrix.SpecialLinearGroup.diag2_coe']
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.reduceFinMk, ite_true, ite_false, Fin.zero_ne_one,
      (show (1 : Fin 2) ≠ 0 from by decide)]
  all_goals dsimp only [z]
  all_goals try rw [unit_value]
  all_goals simp

end ReductiveGroups.SimpleDiagonal
