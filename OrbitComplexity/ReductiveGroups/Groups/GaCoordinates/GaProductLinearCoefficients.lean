import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentCoordinate
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductLogarithm
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootLogarithmDifferential
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Ga Product Linear Coefficients

The first-order coefficient of an ordered Ga product at a parameter
occurring exactly once is the tangent of that Ga factor. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

universe u v
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  {ι : Type v}

private def oneVarInclusion (j : ι) : PUnit.{1} → ι := fun _ => j

private theorem oneVarInclusion_injective (j : ι) :
    Function.Injective (oneVarInclusion j) :=
  fun _ _ _ => Subsingleton.elim _ _

private theorem coeff_single_eq_specialization_coeff_one
    (j : ι) (p : MvPolynomial ι K) :
    p.coeff (Finsupp.single j 1) =
      (MvPolynomial.uniqueAlgEquiv K PUnit.{1}
        (MvPolynomial.killCompl (oneVarInclusion_injective j) p)).coeff 1 := by
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.coeff_killCompl]
  simp [oneVarInclusion]

private theorem specialization_eval
    [DecidableEq ι]
    (j : ι) (p : MvPolynomial ι K) (t : K) :
    (MvPolynomial.uniqueAlgEquiv K PUnit.{1}
      (MvPolynomial.killCompl (oneVarInclusion_injective j) p)).eval t =
      MvPolynomial.aeval (fun i => if i = j then t else 0) p := by
  classical
  let f : PUnit.{1} → ι := oneVarInclusion j
  have hf : Function.Injective f := oneVarInclusion_injective j
  have h : ((Polynomial.aeval t).comp
      (MvPolynomial.uniqueAlgEquiv K PUnit.{1}).toAlgHom).comp
      (MvPolynomial.killCompl hf) =
      MvPolynomial.aeval (fun i : ι => if i = j then t else 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simp [MvPolynomial.killCompl, f, oneVarInclusion, MvPolynomial.uniqueAlgEquiv]
      change Polynomial.eval t
        (MvPolynomial.eval₂ Polynomial.C (fun _ : PUnit.{1} => Polynomial.X)
          (MvPolynomial.X _)) = t
      simp
    · have hji : j ≠ i := Ne.symm hi
      simp [MvPolynomial.killCompl, f, oneVarInclusion, hi, hji]
  exact congrArg (fun φ : MvPolynomial ι K →ₐ[K] K => φ p) h

/-- The coefficient of a parameter occurring exactly once in an ordered
product is the tangent value of that Ga factor. -/
theorem GaProductCoordinate.coeff_single_of_nodup
    [CharZero K]
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (l : List ι)
    (hl : l.Nodup) (j : ι) (hj : j ∈ l) (b : B) :
    (gaProductCoordinate x l b).coeff (Finsupp.single j 1) =
      Bialgebra.CounitAlgebra.algEquivSelf K B K
        (gaAffineGroupTangent (x j) b) := by
  classical
  let p := gaProductCoordinate x l b
  let q := MvPolynomial.uniqueAlgEquiv K PUnit.{1}
    (MvPolynomial.killCompl (oneVarInclusion_injective j) p)
  have hcount : l.count j = 1 := (List.nodup_iff_count_eq_one.mp hl) j hj
  have hprod (t : K) :
      (l.map (fun i => gaParameterPoint (x i) (if i = j then t else 0))).prod =
        gaParameterPoint (x j) t := by
    rw [List.prod_map_eq_pow_single j]
    · simp [hcount]
    · intro i hij _
      simp [hij, gaParameterPoint_zero]
  have hpoly : q = gaPolynomialEquiv K (x j b) := by
    apply Polynomial.funext
    intro t
    rw [specialization_eval]
    have h := congrArg (fun φ : B →ₐ[K] K => φ b)
      (gaProductCoordinate_eval x l (fun i => if i = j then t else 0))
    simp only [AlgHom.comp_apply] at h
    rw [hprod] at h
    rw [gaPolynomialEquiv_eval_point]
    exact h
  rw [coeff_single_eq_specialization_coeff_one]
  change q.coeff 1 = _
  rw [hpoly]
  rw [gaAffineGroupTangent, gaOriginDerivation_comp_apply]

/-- For Borel logarithm coordinates, the same coefficient is
exactly the chosen linear functional applied to the generating tangent. -/
theorem BorelRootProductLogarithm.coeff_single_of_nodup
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    {ι₀ : Type u}
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι₀ →₀ ℤ)))
    (hπ : Function.Surjective π)
    (x : ι → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈
      (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
          (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (l : List ι) (hl : l.Nodup) (j : ι) (hj : j ∈ l)
    (f : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range →ₗ[K] K) :
    (borelRootProductLogarithm J hJ π hπ x l f).coeff
      (Finsupp.single j 1) =
        f ⟨gaAffineGroupTangent (x j), hx j⟩ := by
  let d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range :=
    ⟨gaAffineGroupTangent (x j), hx j⟩
  rw [borelRootProductLogarithm, GaProductCoordinate.coeff_single_of_nodup x l hl j hj]
  exact borelRootLogarithmCoordinate_tangent J hJ π hπ f d

end ReductiveGroups
