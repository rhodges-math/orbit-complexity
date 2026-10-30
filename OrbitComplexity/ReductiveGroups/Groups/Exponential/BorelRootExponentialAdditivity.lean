import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentExponential
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import OrbitComplexity.ReductiveGroups.Lie.Roots.RootProductConjugation

/-!
# Borel Root Exponential Additivity

The Borel root exponential has the usual laws for zero,
inverses, and commuting tangent vectors. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] in
private theorem matrixPointMap_injective (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) :
    Function.Injective
      (fun p : WithConv (B →ₐ[K] K) =>
        GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ p)) := by
  intro p q hpq
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hρ b
  have h := (GeneralLinear.pointsMulEquiv n).injective hpq
  have h' := congrArg (fun z : WithConv
    (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) => z.ofConv a) h
  simpa only [AlgHom.mapDomain_apply_apply] using h'

variable (J : HopfIdeal K B)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
  (hπ : Function.Surjective π)

private abbrev rootTangentSubmodule
    (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :=
  (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ)).hom).range

/-- The original-group exponential of the zero subgroup tangent is identity. -/
@[simp] theorem borelRootUnipotentExponential_zero :
    borelRootUnipotentExponential J hJ π hπ
      (0 : rootTangentSubmodule J π hπ) = 1 := by
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  apply matrixPointMap_injective n ρ hρ
  apply Units.ext
  rw [borelRootUnipotentExponential_matrix]
  have hone : GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ (1 : WithConv (B →ₐ[K] K))) = 1 := by
    rw [map_one, map_one]
  change associativeExponential (K := K)
    (affineGroupMatrixDifferential n ρ (0 : 𝔤)) =
      (GeneralLinear.pointsMulEquiv n
        (AlgHom.mapDomain ρ (1 : WithConv (B →ₐ[K] K))) :
          Matrix (Fin n) (Fin n) K)
  rw [hone]
  simp [associativeExponential]

/-- Additivity holds for commuting original tangents in the Ga-only subgroup. -/
theorem BorelRootUnipotentExponential.add_of_commute
    (d e : rootTangentSubmodule J π hπ)
    (hde : ⁅(d : 𝔤), (e : 𝔤)⁆ = 0) :
    borelRootUnipotentExponential J hJ π hπ (d + e) =
      borelRootUnipotentExponential J hJ π hπ d *
        borelRootUnipotentExponential J hJ π hπ e := by
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  apply matrixPointMap_injective n ρ hρ
  apply Units.ext
  let X := affineGroupMatrixDifferential n ρ (d : 𝔤)
  let Y := affineGroupMatrixDifferential n ρ (e : 𝔤)
  have hX : IsNilpotent X := by
    simpa only [X, borelRootUnipotentGa_tangent] using
      (gaAffineGroupTangent_matrix_nilpotent n
        (borelRootUnipotentGa J hJ π hπ d.val d.property) ρ)
  have hY : IsNilpotent Y := by
    simpa only [Y, borelRootUnipotentGa_tangent] using
      (gaAffineGroupTangent_matrix_nilpotent n
        (borelRootUnipotentGa J hJ π hπ e.val e.property) ρ)
  have hbracket := (affineGroupMatrixDifferential n ρ).map_lie d.val e.val
  rw [hde, map_zero] at hbracket
  change 0 = X * Y - Y * X at hbracket
  have hcomm : Commute X Y := sub_eq_zero.mp hbracket.symm
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) K) :=
    Module.compHom _ (algebraMap ℚ K)
  have hexp : associativeExponential (K := K) (X + Y) =
      associativeExponential (K := K) X * associativeExponential (K := K) Y :=
    IsNilpotent.exp_add_of_commute hcomm hX hY
  simp only [map_mul, borelRootUnipotentExponential_matrix, Units.val_mul]
  change associativeExponential (K := K)
      (affineGroupMatrixDifferential n ρ ((d : 𝔤) + (e : 𝔤))) =
    associativeExponential (K := K) X * associativeExponential (K := K) Y
  rw [map_add]
  exact hexp

/-- The exponential of a negated tangent is the inverse original-group point. -/
@[simp] theorem borelRootUnipotentExponential_neg
    (d : rootTangentSubmodule J π hπ) :
    borelRootUnipotentExponential J hJ π hπ (-d) =
      (borelRootUnipotentExponential J hJ π hπ d)⁻¹ := by
  have h := BorelRootUnipotentExponential.add_of_commute J hJ π hπ
    (-d) d (by simp)
  exact mul_eq_one_iff_eq_inv.mp (by simpa using h.symm)

end ReductiveGroups
