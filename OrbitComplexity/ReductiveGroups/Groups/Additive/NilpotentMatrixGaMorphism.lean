import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentOneParameterSubgroup
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints

/-!
# Nilpotent Matrix Ga Morphism

The finite exponential of a nilpotent matrix gives an additive-group
coordinate morphism into the general linear group. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

private def exponentialMatrix {A : Type*} [CommRing A] [Algebra K A]
    (X : Matrix (Fin n) (Fin n) K) (a : A) : Matrix (Fin n) (Fin n) A :=
  associativeExponential (K := K) (a • X.map (algebraMap K A))

omit [CharZero K] in
private theorem exponentialMatrix_nilpotent {A : Type*} [CommRing A] [Algebra K A]
    {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) (a : A) :
    IsNilpotent (a • X.map (algebraMap K A)) :=
  (hX.map (algebraMap K A).mapMatrix).smul a

private theorem exponentialMatrix_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B)
    {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) (a : A) :
    (exponentialMatrix X a).map f = exponentialMatrix X (f a) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) A) :=
    Module.compHom (Matrix (Fin n) (Fin n) A) (algebraMap ℚ K)
  let : Module ℚ (Matrix (Fin n) (Fin n) B) :=
    Module.compHom (Matrix (Fin n) (Fin n) B) (algebraMap ℚ K)
  change (f.mapMatrix) (IsNilpotent.exp (a • X.map (algebraMap K A))) =
    IsNilpotent.exp ((f a) • X.map (algebraMap K B))
  rw [(exponentialMatrix_nilpotent hX a).map_exp f.mapMatrix]
  congr 1
  ext i j
  simp [Matrix.smul_apply]

private theorem exponentialMatrix_add {A : Type*} [CommRing A] [Algebra K A]
    {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) (a b : A) :
    exponentialMatrix X (a + b) = exponentialMatrix X a * exponentialMatrix X b := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) A) :=
    Module.compHom (Matrix (Fin n) (Fin n) A) (algebraMap ℚ K)
  change IsNilpotent.exp ((a + b) • X.map (algebraMap K A)) =
    IsNilpotent.exp (a • X.map (algebraMap K A)) *
      IsNilpotent.exp (b • X.map (algebraMap K A))
  rw [add_smul]
  exact IsNilpotent.exp_add_of_commute
    ((Commute.refl (X.map (algebraMap K A))).smul_left a |>.smul_right b)
    (exponentialMatrix_nilpotent hX a) (exponentialMatrix_nilpotent hX b)

private theorem exponentialMatrix_zero {A : Type*} [CommRing A] [Algebra K A]
    (X : Matrix (Fin n) (Fin n) K) : exponentialMatrix X (0 : A) = 1 := by
  simp [exponentialMatrix, associativeExponential]

private def exponentialMatrixUnit {A : Type*} [CommRing A] [Algebra K A]
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) (a : A) :
    Matrix.GeneralLinearGroup (Fin n) A :=
  Matrix.GeneralLinearGroup.mk'' (exponentialMatrix X a) (by
    let : Algebra ℚ K := (Rat.castHom K).toAlgebra
    let : Module ℚ (Matrix (Fin n) (Fin n) A) :=
      Module.compHom (Matrix (Fin n) (Fin n) A) (algebraMap ℚ K)
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (IsNilpotent.isUnit_exp (exponentialMatrix_nilpotent hX a)))

private def nilpotentMatrixGaAlgHom (X : Matrix (Fin n) (Fin n) K)
    (hX : IsNilpotent X) :
    TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] SymmetricAlgebra K K :=
  (TauCeti.GeneralLinear.generalLinearToPoint (R := K) n
    (exponentialMatrixUnit X hX (SymmetricAlgebra.ι K K 1))).ofConv

private theorem nilpotentMatrixGaAlgHom_X (X : Matrix (Fin n) (Fin n) K)
    (hX : IsNilpotent X) (i j : Fin n) :
    nilpotentMatrixGaAlgHom X hX
      (TauCeti.GeneralLinear.genericMatrix K n i j) =
      exponentialMatrix X (SymmetricAlgebra.ι K K 1) i j := by
  simp [nilpotentMatrixGaAlgHom, TauCeti.GeneralLinear.genericMatrix_apply,
    exponentialMatrixUnit]

private theorem nilpotentMatrixGaAlgHom_counit
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K K)).comp
        (nilpotentMatrixGaAlgHom X hX) =
      Bialgebra.counitAlgHom K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) := by
  apply TauCeti.GeneralLinear.coordinateHopfAlgebra_algHom_ext K n
  intro i j
  have h := exponentialMatrix_map
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K K)) hX
    (SymmetricAlgebra.ι K K 1)
  have hzero : Coalgebra.counit (R := K) (SymmetricAlgebra.ι K K 1) = 0 :=
    SymmetricAlgebra.counit_ι (R := K) (M := K) (1 : K)
  rw [Bialgebra.counitAlgHom_apply, hzero, exponentialMatrix_zero] at h
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) h
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
  rw [← TauCeti.GeneralLinear.genericMatrix_apply,
    nilpotentMatrixGaAlgHom_X]
  simpa only [TauCeti.GeneralLinear.genericMatrix_apply,
    Bialgebra.counitAlgHom_apply,
    TauCeti.GeneralLinear.coordinateHopfAlgebra_counit_X,
    Matrix.map_apply, Matrix.one_apply] using hij

private theorem nilpotentMatrixGaAlgHom_comul
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) :
    (Algebra.TensorProduct.map (nilpotentMatrixGaAlgHom X hX)
      (nilpotentMatrixGaAlgHom X hX)).comp
        (Bialgebra.comulAlgHom K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)) =
      (Bialgebra.comulAlgHom K (SymmetricAlgebra K K)).comp
        (nilpotentMatrixGaAlgHom X hX) := by
  apply TauCeti.GeneralLinear.coordinateHopfAlgebra_algHom_ext K n
  intro i j
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    TauCeti.GeneralLinear.coordinateHopfAlgebra_comul_X, map_sum,
    Algebra.TensorProduct.map_tmul]
  simp only [← TauCeti.GeneralLinear.genericMatrix_apply,
    nilpotentMatrixGaAlgHom_X]
  have hcomul := exponentialMatrix_map
    (Bialgebra.comulAlgHom K (SymmetricAlgebra K K)) hX
    (SymmetricAlgebra.ι K K 1)
  let fL : SymmetricAlgebra K K →ₐ[K]
      (SymmetricAlgebra K K ⊗[K] SymmetricAlgebra K K) :=
    Algebra.TensorProduct.includeLeft
  let fR : SymmetricAlgebra K K →ₐ[K]
      (SymmetricAlgebra K K ⊗[K] SymmetricAlgebra K K) :=
    Algebra.TensorProduct.includeRight
  have hleft := exponentialMatrix_map
    fL hX
    (SymmetricAlgebra.ι K K 1)
  have hright := exponentialMatrix_map
    fR hX
    (SymmetricAlgebra.ι K K 1)
  rw [Bialgebra.comulAlgHom_apply, SymmetricAlgebra.comul_ι] at hcomul
  have hsum := exponentialMatrix_add hX
    ((SymmetricAlgebra.ι K K 1) ⊗ₜ[K] (1 : SymmetricAlgebra K K))
    ((1 : SymmetricAlgebra K K) ⊗ₜ[K] (SymmetricAlgebra.ι K K 1))
  have hmatrix :
      (exponentialMatrix X (SymmetricAlgebra.ι K K 1)).map
          (Bialgebra.comulAlgHom K (SymmetricAlgebra K K)) =
        (exponentialMatrix X (SymmetricAlgebra.ι K K 1)).map
            fL *
          (exponentialMatrix X (SymmetricAlgebra.ι K K 1)).map
            fR := by
    rw [hcomul, hleft, hright]
    exact hsum
  simpa [Matrix.mul_apply, Matrix.map_apply, fL, fR,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul] using
    (congrArg (fun M => M i j) hmatrix).symm

/-- The coordinate bialgebra map of the finite nilpotent matrix exponential. -/
def nilpotentMatrixGaMorphism (X : Matrix (Fin n) (Fin n) K)
    (hX : IsNilpotent X) :
    TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] SymmetricAlgebra K K :=
  BialgHom.ofAlgHom (nilpotentMatrixGaAlgHom X hX)
    (nilpotentMatrixGaAlgHom_counit X hX)
    (nilpotentMatrixGaAlgHom_comul X hX)

/-- The equality is

```lean
nilpotentMatrixGaMorphism X hX (TauCeti.GeneralLinear.genericMatrix K n i j) =
      exponentialMatrix X (SymmetricAlgebra.ι K K 1) i j
```
-/
theorem nilpotentMatrixGaMorphism_X
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) (i j : Fin n) :
    nilpotentMatrixGaMorphism X hX (TauCeti.GeneralLinear.genericMatrix K n i j) =
      exponentialMatrix X (SymmetricAlgebra.ι K K 1) i j :=
  nilpotentMatrixGaAlgHom_X X hX i j

/-- The matrix of the point at parameter `t` is the finite exponential of `tX`. -/
theorem nilpotentMatrixGaMorphism_points
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) (t : K) :
    (gaMatrixPoints n (nilpotentMatrixGaMorphism X hX)
      (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) =
      associativeExponential (K := K) (t • X) := by
  let q := (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)
  have hmap := exponentialMatrix_map q.ofConv hX (SymmetricAlgebra.ι K K 1)
  have hqt : q.ofConv (SymmetricAlgebra.ι K K 1) = t := by
    simp [q, TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι]
  rw [hqt] at hmap
  have hbase : exponentialMatrix X t = associativeExponential (K := K) (t • X) := by
    congr 1
  rw [hbase] at hmap
  ext i j
  have hφ : nilpotentMatrixGaMorphism X hX
      (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
        (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))) =
      exponentialMatrix X (SymmetricAlgebra.ι K K 1) i j := by
    simpa only [TauCeti.GeneralLinear.genericMatrix_apply] using
      nilpotentMatrixGaMorphism_X X hX i j
  simpa [gaMatrixPoints, q, Function.comp_def, TauCeti.AlgHom.mapDomain_apply,
    TauCeti.GeneralLinear.pointsMulEquiv_apply,
    TauCeti.GeneralLinear.pointToGeneralLinear_apply, hφ, Matrix.map_apply] using
    congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hmap

private theorem exponentialMatrix_generator_coeff_one
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) (i j : Fin n) :
    (gaPolynomialEquiv K
      (exponentialMatrix X (SymmetricAlgebra.ι K K 1) i j)).coeff 1 = X i j := by
  let z : SymmetricAlgebra K K := SymmetricAlgebra.ι K K 1
  let Y : Matrix (Fin n) (Fin n) (SymmetricAlgebra K K) :=
    z • X.map (algebraMap K (SymmetricAlgebra K K))
  obtain ⟨m, hm⟩ := hX
  have hYm : Y ^ m = 0 := by
    simp [Y, smul_pow, ← Matrix.map_pow, hm]
  have hYbig : Y ^ (m + 2) = 0 := by
    rw [pow_add, hYm, zero_mul]
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) (SymmetricAlgebra K K)) :=
    Module.compHom (Matrix (Fin n) (Fin n) (SymmetricAlgebra K K)) (algebraMap ℚ K)
  change (gaPolynomialEquiv K (IsNilpotent.exp Y i j)).coeff 1 = X i j
  rw [IsNilpotent.exp_eq_sum hYbig, Matrix.sum_apply]
  simp only [map_sum, Polynomial.finsetSum_coeff]
  have hterm (b : ℕ) :
      ((gaPolynomialEquiv K) (((b.factorial : ℚ)⁻¹ • Y ^ b) i j)).coeff 1 =
        if b = 1 then X i j else 0 := by
    have hpow : Y ^ b = z ^ b • (X ^ b).map (algebraMap K (SymmetricAlgebra K K)) := by
      simp [Y, smul_pow, ← Matrix.map_pow]
    rw [hpow, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply]
    change ((gaPolynomialEquiv K)
      ((algebraMap ℚ K ((b.factorial : ℚ)⁻¹)) •
        (z ^ b • algebraMap K (SymmetricAlgebra K K) ((X ^ b) i j)))).coeff 1 = _
    change ((gaPolynomialEquiv K)
      (algebraMap K (SymmetricAlgebra K K)
          (algebraMap ℚ K ((b.factorial : ℚ)⁻¹)) *
        (z ^ b * algebraMap K (SymmetricAlgebra K K) ((X ^ b) i j)))).coeff 1 = _
    simp only [map_mul, map_pow]
    rw [(gaPolynomialEquiv K).commutes, (gaPolynomialEquiv K).commutes]
    split_ifs with hb
    · subst b
      simp [z, gaPolynomialEquiv_generator]
    · have hb' : 1 ≠ b := Ne.symm hb
      simp [z, gaPolynomialEquiv_generator, Polynomial.coeff_X_pow, hb']
  calc
    (∑ b ∈ Finset.range (m + 2),
      ((gaPolynomialEquiv K) (((b.factorial : ℚ)⁻¹ • Y ^ b) i j)).coeff 1) =
        ∑ b ∈ Finset.range (m + 2), if b = 1 then X i j else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hterm b
    _ = X i j := by
      simp [Finset.sum_ite_eq', Finset.mem_range, show 1 < m + 2 by omega]

/-- The differential of the constructed Ga morphism is the prescribed matrix. -/
theorem nilpotentMatrixGaMorphism_tangent
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X) :
    TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K) (nilpotentMatrixGaMorphism X hX)
        (gaOriginDerivation K)) = X := by
  rw [← GaMatrixPolynomial.coeff_one_differential]
  ext i j
  simp only [gaMatrixPolynomial, matPolyEquiv_coeff_apply, Matrix.map_apply,
    nilpotentMatrixGaMorphism_X]
  exact exponentialMatrix_generator_coeff_one X hX i j

end ReductiveGroups


