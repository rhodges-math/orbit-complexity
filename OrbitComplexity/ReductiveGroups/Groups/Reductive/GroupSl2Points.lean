import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2

/-! # Simple `SL₂` morphisms and their matrix points -/

noncomputable section

namespace ReductiveGroups

open TauCeti WithConv
open scoped Matrix

universe u

/-- The determinant-one Weyl matrix with entries `0, -1, 1, 0`. -/
def sl2Weyl (K : Type u) [CommRing K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

variable {K : Type u} [Field K]

private theorem elementary_point {i j : Fin 2} (hij : i ≠ j) (t : K) :
    (TauCeti.SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm
        (Matrix.SpecialLinearGroup.transvection hij t) =
      gaAffineGroupPoints (TauCeti.SpecialLinear.rootSubgroupCoordinateMap
        (R := K) hij).hom (Multiplicative.ofAdd t) := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)
  have h := TauCeti.SpecialLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app
    hij (CommAlgCat.of K K) q
  change AlgHom.mapDomain
      (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom q =
    TauCeti.SpecialLinear.rootSubgroupPoints hij q at h
  apply (TauCeti.SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).injective
  rw [MulEquiv.apply_symm_apply]
  change Matrix.SpecialLinearGroup.transvection hij t =
    TauCeti.SpecialLinear.pointsMulEquiv (R := K) (A := K) 2
      (AlgHom.mapDomain (TauCeti.SpecialLinear.rootSubgroupCoordinateMap
        (R := K) hij).hom q)
  rw [h, TauCeti.SpecialLinear.pointsMulEquiv_rootSubgroupPoints]
  simp [q]

private theorem weyl_factor :
    sl2Weyl K = (Matrix.SpecialLinearGroup.transvection
        (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K) *
      Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1 : K) *
      Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K))⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  change (!![0, -1; 1, 0] *
    ((1 + Matrix.single (0 : Fin 2) 1 (1 : K)) *
      (1 + Matrix.single (1 : Fin 2) 0 (-1 : K)) *
      (1 + Matrix.single (0 : Fin 2) 1 (1 : K)))) =
        (1 : Matrix (Fin 2) (Fin 2) K)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

private theorem minus_one_factor :
    Matrix.SpecialLinearGroup.diag2 (-1 : K) (neg_ne_zero.mpr one_ne_zero) =
      (Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K) *
        Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1 : K) *
        Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K)) ^ 2 := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pow_two, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.diag2_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

namespace ReductiveGroupData

variable [CharZero K] [IsAlgClosed K] (G : ReductiveGroupData K)

/-- The coordinate morphism from the simple `SL₂` group through its chosen root pair. -/
def simpleSl2Map (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] TauCeti.SpecialLinear.coordinateHopfAlgebra K 2 :=
  (G.exists_simpleSl2Map i).choose

/-- The upper elementary subgroup is the chosen positive simple subgroup. -/
theorem simpleSl2Map_upper (i : G.rootBase.support) :
    (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K)
        (zero_ne_one : (0 : Fin 2) ≠ 1)).hom.comp (G.simpleSl2Map i) = G.simpleRootMap i :=
  (G.exists_simpleSl2Map i).choose_spec.1

/-- The lower elementary subgroup is the chosen negative simple subgroup. -/
theorem simpleSl2Map_lower (i : G.rootBase.support) :
    (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K)
        (one_ne_zero : (1 : Fin 2) ≠ 0)).hom.comp (G.simpleSl2Map i) =
      G.negativeSimpleRootMap i :=
  (G.exists_simpleSl2Map i).choose_spec.2.1

/-- The differential agrees with the homomorphism of the chosen simple-root triple. -/
theorem simpleSl2Map_differential (i : G.rootBase.support)
    (x : LieAlgebra.SpecialLinear.sl (Fin 2) K) :
    derivationComp (B := K) (G.simpleSl2Map i)
        ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) =
      G.simpleSl2LieHom i x :=
  (G.exists_simpleSl2Map i).choose_spec.2.2 x

/-- The homomorphism on rational matrix points of the chosen simple `SL₂`. -/
def simpleSl2Points (i : G.rootBase.support) :
    Matrix.SpecialLinearGroup (Fin 2) K →* G.points :=
  (AlgHom.mapDomain (G.simpleSl2Map i)).comp
    (TauCeti.SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm.toMonoidHom

/-- An upper transvection maps to its chosen positive simple-root parameter. -/
theorem simpleSl2Points_upper (i : G.rootBase.support) (t : K) :
    G.simpleSl2Points i (Matrix.SpecialLinearGroup.transvection
        (zero_ne_one : (0 : Fin 2) ≠ 1) t) =
      gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd t) := by
  change AlgHom.mapDomain (G.simpleSl2Map i)
    ((TauCeti.SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm
      (Matrix.SpecialLinearGroup.transvection
        (zero_ne_one : (0 : Fin 2) ≠ 1) t)) = _
  rw [elementary_point]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  exact congrArg
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
      (Multiplicative.ofAdd t)).ofConv
    (congrArg (fun f : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K => f a)
      (G.simpleSl2Map_upper i))

/-- A lower transvection maps to its chosen negative simple-root parameter. -/
theorem simpleSl2Points_lower (i : G.rootBase.support) (t : K) :
    G.simpleSl2Points i (Matrix.SpecialLinearGroup.transvection
        (one_ne_zero : (1 : Fin 2) ≠ 0) t) =
      gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd t) := by
  change AlgHom.mapDomain (G.simpleSl2Map i)
    ((TauCeti.SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm
      (Matrix.SpecialLinearGroup.transvection
        (one_ne_zero : (1 : Fin 2) ≠ 0) t)) = _
  rw [elementary_point]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  exact congrArg
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
      (Multiplicative.ofAdd t)).ofConv
    (congrArg (fun f : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K => f a)
      (G.simpleSl2Map_lower i))

/-- The matrix `[[0,-1],[1,0]]` maps to the inverse simple reflection representative. -/
theorem simpleSl2Points_weyl (i : G.rootBase.support) :
    G.simpleSl2Points i (sl2Weyl K) = (G.reflectionPoint i.val)⁻¹ := by
  rw [weyl_factor, map_inv, map_mul, map_mul,
    simpleSl2Points_upper, simpleSl2Points_lower]
  rfl

/-- The central matrix `-I` maps to the square of the fixed simple representative. -/
theorem simpleSl2Points_square (i : G.rootBase.support) :
    G.simpleSl2Points i
        (Matrix.SpecialLinearGroup.diag2 (-1 : K) (neg_ne_zero.mpr one_ne_zero)) =
      G.reflectionPoint i.val ^ 2 := by
  rw [minus_one_factor, map_pow, map_mul, map_mul,
    simpleSl2Points_upper, simpleSl2Points_lower]
  rfl

end ReductiveGroupData

end ReductiveGroups
