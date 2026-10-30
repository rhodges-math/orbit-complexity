import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateAction
import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateGenerators
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# GL Coordinate Semisimple

Eigenvector calculus for the left tangent derivation of GL coordinates.
These identities are used after diagonalizing the finite row representation. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] (n : ℕ)
variable (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
  (TauCeti.Bialgebra.CounitAlgebra K
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))

private theorem matrix_aeval_transpose (A : Matrix (Fin n) (Fin n) K)
    (p : Polynomial K) :
    (Polynomial.aeval A.transpose p) = (Polynomial.aeval A p).transpose := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  simp only [Matrix.transpose_sum, Matrix.transpose_pow, Matrix.transpose_smul]

private theorem matrix_semisimple_transpose
    (A : Matrix (Fin n) (Fin n) K)
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    Module.End.IsSemisimple (Matrix.toLin' A.transpose) := by
  let p : Polynomial K := minpoly K A
  have hp : Squarefree p := by
    simpa only [p, Matrix.minpoly_toLin'] using hA.minpoly_squarefree
  have hmatrix : Polynomial.aeval A.transpose p = 0 := by
    rw [matrix_aeval_transpose]
    simp only [p, minpoly.aeval, Matrix.transpose_zero]
  have hend : Polynomial.aeval (Matrix.toLin' A.transpose) p = 0 := by
    change Polynomial.aeval ((Matrix.toLinAlgEquiv' :
      Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)) A.transpose) p = 0
    rw [Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' :
      Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K))]
    simp only [hmatrix, map_zero]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp hend

private theorem isSemisimple_of_eigenspace_iSup_eq_top
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : Module.End K V)
    (hspan : (⨆ ξ : K, Module.End.eigenspace f ξ) = ⊤) :
    Module.End.IsSemisimple f := by
  let P (ξ : K) : Submodule (Polynomial K) (Module.AEval' f) :=
    Module.AEval.mapSubmodule K V f
      ⟨Module.End.eigenspace f ξ, Module.End.eigenspace_mem_invtSubmodule f ξ⟩
  have hP (ξ : K) : IsSemisimpleModule (Polynomial K) (P ξ) := by
    have heig : Module.End.IsSemisimple
        (f.restrict (Module.End.eigenspace_mem_invtSubmodule f ξ)) := by
      rw [Module.End.restrict_eigenspace]
      exact Module.End.IsSemisimple_smul ξ Module.End.isSemisimple_id
    exact (Module.AEval.restrict_equiv_mapSubmodule f
      (Module.End.eigenspace f ξ)
      (Module.End.eigenspace_mem_invtSubmodule f ξ)).isSemisimpleModule_iff.mp heig
  have htop : (⨆ ξ : K, P ξ) = ⊤ := by
    apply top_unique
    intro z _
    let Q : Submodule (Polynomial K) (Module.AEval' f) := ⨆ ξ, P ξ
    have hle (ξ : K) : Module.End.eigenspace f ξ ≤
        (((Module.AEval.mapSubmodule K V f).symm Q : f.invtSubmodule) :
          Submodule K V) := by
      have hh := (Module.AEval.mapSubmodule K V f).symm.monotone
        (le_iSup P ξ)
      simp only [P, OrderIso.symm_apply_apply] at hh
      exact hh
    have hz : (Module.AEval.of K V f).symm z ∈
        (((Module.AEval.mapSubmodule K V f).symm Q : f.invtSubmodule) :
          Submodule K V) := by
      apply (iSup_le hle)
      rw [hspan]
      trivial
    have hz' : z ∈ Q := by
      simpa only [Module.AEval.mem_mapSubmodule_symm_apply,
        LinearEquiv.apply_symm_apply] using hz
    exact hz'
  exact isSemisimpleModule_of_isSemisimpleModule_submodule' hP htop

/-- Products of coordinate eigenvectors are eigenvectors, with the
sum of the two weights. -/
theorem leftTangentOperator_mul_eigenvectors
    (a b : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (ξ η : K)
    (ha : leftTangentOperator d a = ξ • a)
    (hb : leftTangentOperator d b = η • b) :
    leftTangentOperator d (a * b) = (ξ + η) • (a * b) := by
  rw [leftTangentOperator_mul, ha, hb]
  simp only [Algebra.smul_def]
  rw [map_add]
  ring

/-- Powers of a coordinate eigenvector have the expected weight. -/
theorem leftTangentOperator_pow_eigenvector
    (a : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (ξ : K)
    (ha : leftTangentOperator d a = ξ • a) (r : ℕ) :
    leftTangentOperator d (a ^ r) = ((r : K) * ξ) • (a ^ r) := by
  induction r with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, zero_smul]
      change leftTangentOperator d 1 = 0
      exact (leftTangentDerivation d).map_one_eq_zero
  | succ r ih =>
      rw [pow_succ]
      have h := leftTangentOperator_mul_eigenvectors n d (a ^ r) a
        ((r : K) * ξ) ξ ih ha
      convert h using 1
      · rw [Nat.cast_succ]
        ring_nf

/-- Finite products of coordinate eigenvectors have the summed weight. -/
theorem leftTangentOperator_prod_eigenvectors
    {ι : Type*} (s : Finset ι)
    (a : ι → TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
    (ξ : ι → K)
    (ha : ∀ i ∈ s, leftTangentOperator d (a i) = ξ i • a i) :
    leftTangentOperator d (∏ i ∈ s, a i) =
      (∑ i ∈ s, ξ i) • (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, zero_smul]
      change (leftTangentDerivation d) 1 = 0
      exact (leftTangentDerivation d).map_one_eq_zero
  | @insert i s his ih =>
      have hs : ∀ j ∈ s, leftTangentOperator d (a j) = ξ j • a j :=
        fun j hj => ha j (Finset.mem_insert_of_mem hj)
      simp only [Finset.prod_insert his, Finset.sum_insert his]
      exact leftTangentOperator_mul_eigenvectors n d (a i) (∏ j ∈ s, a j)
        (ξ i) (∑ j ∈ s, ξ j) (ha i (Finset.mem_insert_self i s)) (ih hs)

/-- The span of left-tangent eigenvectors. -/
def glLeftEigenSpan : Submodule K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) :=
  Submodule.span K {a | ∃ ξ : K, leftTangentOperator d a = ξ • a}

/-- For these parameters,

```lean
a * b ∈ glLeftEigenSpan n d
```
-/
theorem glLeftEigenSpan_mul_mem
    {a b : TauCeti.GeneralLinear.coordinateHopfAlgebra K n}
    (ha : a ∈ glLeftEigenSpan n d) (hb : b ∈ glLeftEigenSpan n d) :
    a * b ∈ glLeftEigenSpan n d := by
  unfold glLeftEigenSpan at ha hb ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · intro y hy
      obtain ⟨ξ, hξ⟩ := hx
      obtain ⟨η, hη⟩ := hy
      exact Submodule.subset_span ⟨ξ + η,
        leftTangentOperator_mul_eigenvectors n d x y ξ η hξ hη⟩
    · simp
    · intro y z _ _ hy hz
      simpa only [mul_add] using (Submodule.add_mem _ hy hz)
    · intro r y _ hy
      simpa only [mul_smul_comm] using (Submodule.smul_mem _ r hy)
  · simp
  · intro x y _ _ hx hy
    simpa only [add_mul] using (Submodule.add_mem _ hx hy)
  · intro r x _ hx
    simpa only [smul_mul_assoc] using (Submodule.smul_mem _ r hx)

/-- For these parameters,

```lean
(1 : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) ∈ glLeftEigenSpan n d
```
-/
theorem glLeftEigenSpan_one :
    (1 : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) ∈ glLeftEigenSpan n d := by
  apply Submodule.subset_span
  refine ⟨0, ?_⟩
  change (leftTangentDerivation d) 1 = 0 • (1 :
    TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
  simpa only [zero_smul] using (leftTangentDerivation d).map_one_eq_zero

/-- For these parameters,

```lean
algebraMap K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) c ∈
      glLeftEigenSpan n d
```
-/
theorem glLeftEigenSpan_algebraMap (c : K) :
    algebraMap K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) c ∈
      glLeftEigenSpan n d := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (glLeftEigenSpan n d).smul_mem c (glLeftEigenSpan_one n d)

/-- The span of eigenvectors is a subalgebra of GL coordinates. -/
def glLeftEigenSubalgebra :
    Subalgebra K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) where
  carrier := glLeftEigenSpan n d
  zero_mem' := (glLeftEigenSpan n d).zero_mem
  one_mem' := glLeftEigenSpan_one n d
  add_mem' := fun ha hb => (glLeftEigenSpan n d).add_mem ha hb
  mul_mem' := fun ha hb => glLeftEigenSpan_mul_mem n d ha hb
  algebraMap_mem' := glLeftEigenSpan_algebraMap n d

/-- If GL coordinates are generated by left-tangent eigenvectors,
their eigenspaces span the whole coordinate algebra. -/
theorem glLeftEigenSpan_eq_top_of_adjoin
    (S : Set (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))
    (hS : ∀ a ∈ S, ∃ ξ : K, leftTangentOperator d a = ξ • a)
    (hgen : Algebra.adjoin K S = ⊤) : glLeftEigenSpan n d = ⊤ := by
  have hle : Algebra.adjoin K S ≤ glLeftEigenSubalgebra n d := by
    apply Algebra.adjoin_le_iff.mpr
    intro a ha
    exact Submodule.subset_span (hS a ha)
  apply top_unique
  intro a _
  apply hle
  rw [hgen]
  trivial

/-- A linear form in one column of the generic GL matrix. -/
def glRowLinearCoordinate (v : Fin n → K) (j : Fin n) :
    TauCeti.GeneralLinear.coordinateHopfAlgebra K n :=
  ∑ i : Fin n, v i • TauCeti.GeneralLinear.genericMatrix K n i j

/-- The column coordinate map is linear in its row coefficients. -/
def glRowLinearCoordinateLinear (j : Fin n) :
    (Fin n → K) →ₗ[K] TauCeti.GeneralLinear.coordinateHopfAlgebra K n where
  toFun v := glRowLinearCoordinate n v j
  map_add' v w := by
    simp [glRowLinearCoordinate, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [glRowLinearCoordinate, Finset.smul_sum, smul_smul]

/-- A left eigenvector of the tangent matrix produces an eigenvector
of the left tangent derivation on each generic-matrix column. -/
theorem LeftTangentOperator.rowLinearCoordinate_eigenvector
    (v : Fin n → K) (j : Fin n) (ξ : K)
    (hv : ∀ k : Fin n,
      (∑ i : Fin n, v i * TauCeti.GeneralLinear.tangentMatrix n d i k) =
        ξ * v k) :
    leftTangentOperator d (glRowLinearCoordinate n v j) =
      ξ • glRowLinearCoordinate n v j := by
  unfold glRowLinearCoordinate
  simp only [map_sum, map_smul]
  conv_lhs =>
    arg 2
    ext i
    rw [leftTangentOperator_genericMatrix_apply n d i j]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  exact Finset.sum_congr rfl (fun k _ => congrArg
    (fun c : K => c • TauCeti.GeneralLinear.genericMatrix K n k j) (hv k))

/-- Semisimplicity of the transposed matrix makes every generic coordinate a
linear combination of left-tangent eigenvectors. -/
theorem glLeftEigenSpan_genericMatrix
    [IsAlgClosed K]
    (hX : Module.End.IsSemisimple
      (Matrix.toLin' (TauCeti.GeneralLinear.tangentMatrix n d).transpose))
    (i j : Fin n) :
    TauCeti.GeneralLinear.genericMatrix K n i j ∈ glLeftEigenSpan n d := by
  classical
  let P : Submodule K (Fin n → K) :=
    (glLeftEigenSpan n d).comap (glRowLinearCoordinateLinear n j)
  have heig (ξ : K) :
      Module.End.eigenspace
        (Matrix.toLin' (TauCeti.GeneralLinear.tangentMatrix n d).transpose) ξ ≤
        P := by
    intro v hv
    change glRowLinearCoordinate n v j ∈ glLeftEigenSpan n d
    apply Submodule.subset_span
    refine ⟨ξ, LeftTangentOperator.rowLinearCoordinate_eigenvector n d v j ξ ?_⟩
    intro k
    have he := Module.End.mem_eigenspace_iff.mp hv
    have hk := congrFun he k
    calc
      (∑ i : Fin n, v i * TauCeti.GeneralLinear.tangentMatrix n d i k) =
          ∑ i : Fin n, TauCeti.GeneralLinear.tangentMatrix n d i k * v i := by
            apply Finset.sum_congr rfl
            intro i _
            exact mul_comm _ _
      _ = ξ * v k := by
        simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
          Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul] using hk
  have hP : P = ⊤ := by
    apply top_unique
    rw [← hX.iSup_eigenspace_eq_top]
    exact iSup_le heig
  have hi : (Pi.single i (1 : K)) ∈ P := by rw [hP]; trivial
  change glRowLinearCoordinate n (Pi.single i (1 : K)) j ∈
    glLeftEigenSpan n d at hi
  simpa [glRowLinearCoordinate, Pi.single_apply] using hi

/-- Semisimplicity of the tangent matrix makes the full GL coordinate
algebra spanned by eigenvectors of left differentiation. -/
theorem glLeftEigenSpan_eq_top [IsAlgClosed K]
    (hX : Module.End.IsSemisimple
      (Matrix.toLin' (TauCeti.GeneralLinear.tangentMatrix n d))) :
    glLeftEigenSpan n d = ⊤ := by
  have hXt := matrix_semisimple_transpose n
    (TauCeti.GeneralLinear.tangentMatrix n d) hX
  have hS : glLeftEigenSubalgebra n d = ⊤ := by
    apply glCoordinate_subalgebra_eq_top n
    · intro i j
      exact glLeftEigenSpan_genericMatrix n d hXt i j
    · apply Submodule.subset_span
      exact ⟨_, leftTangentOperator_detInverseCoordinate n d⟩
  apply top_unique
  intro a _
  have ha : a ∈ glLeftEigenSubalgebra n d := by rw [hS]; trivial
  exact ha

/-- The GL left tangent operator is semisimple whenever its matrix
is semisimple. The coordinate algebra need not be finite-dimensional. -/
theorem leftTangentOperator_isSemisimple [IsAlgClosed K]
    (hX : Module.End.IsSemisimple
      (Matrix.toLin' (TauCeti.GeneralLinear.tangentMatrix n d))) :
    Module.End.IsSemisimple (leftTangentOperator d) := by
  apply isSemisimple_of_eigenspace_iSup_eq_top
  apply top_unique
  have hspan := glLeftEigenSpan_eq_top n d hX
  intro a _
  have ha : a ∈ glLeftEigenSpan n d := by rw [hspan]; trivial
  have hle : glLeftEigenSpan n d ≤
      (⨆ ξ : K, Module.End.eigenspace (leftTangentOperator d) ξ) := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨ξ, hξ⟩ := hx
    exact Submodule.mem_iSup_of_mem ξ (Module.End.mem_eigenspace_iff.mpr hξ)
  exact hle ha

/-- A multiplicative inverse of a coordinate eigenvector has the
opposite weight. -/
theorem leftTangentOperator_inverse_eigenvector
    (a b : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (ξ : K)
    (hab : a * b = 1)
    (ha : leftTangentOperator d a = ξ • a) :
    leftTangentOperator d b = (-ξ) • b := by
  have h := congrArg (leftTangentOperator d) hab
  rw [leftTangentOperator_mul, ha,
    show leftTangentOperator d
      (1 : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) = 0 from
        (leftTangentDerivation d).map_one_eq_zero] at h
  have h' : a * leftTangentOperator d b = -(b * (ξ • a)) :=
    eq_neg_of_add_eq_zero_left h
  calc
    leftTangentOperator d b = (a * b) * leftTangentOperator d b := by rw [hab, one_mul]
    _ = b * (a * leftTangentOperator d b) := by ring
    _ = b * (-(b * (ξ • a))) := by rw [h']
    _ = (-ξ) • b := by
      rw [Algebra.smul_def, Algebra.smul_def]
      -- Multiplying the eigen-relation for `a` by its inverse leaves `b`.
      calc
        b * -(b * ((algebraMap K _ ) ξ * a)) =
            -(b * b * ((algebraMap K _) ξ * a)) := by ring
        _ = -((algebraMap K _) ξ * b) := by
          rw [show b * b * ((algebraMap K _) ξ * a) =
            (algebraMap K _) ξ * b by
              calc
                b * b * ((algebraMap K _) ξ * a) =
                    ((algebraMap K _) ξ * b) * (a * b) := by ring
                _ = (algebraMap K _) ξ * b := by rw [hab, mul_one]]
        _ = (algebraMap K _) (-ξ) * b := by rw [map_neg, neg_mul]

end ReductiveGroups
