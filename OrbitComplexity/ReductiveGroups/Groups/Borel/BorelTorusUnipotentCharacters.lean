import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusCharacterMonomialRelations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Borel Torus Unipotent Characters

Two facts about field-valued points of a finite-rank split torus
`Spec K[M]`, `M = ℤ^(ι)` written multiplicatively.

1. A coordinate function `F ∈ K[M]` whose values are multiplicative in the
   convolution product of points, and which is nonzero, agrees at every
   point with a single character. The proof uses only point separation of
   the reduced finite-type algebra `K[M]`.
2. Prescribed unit values at an arbitrary finite family of characters are
   realized by a point exactly when they satisfy every integral monomial
   relation satisfied by the characters (Baer extension, since `Kˣ` is
   divisible). The independent-family case is
   `exists_torusPoint_character_values`. -/

noncomputable section
namespace ReductiveGroups.TorusUnipotent

open TauCeti WithConv

universe u

variable {K ι : Type u} [Field K]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Convolution products of torus points multiply character values. -/
theorem torusPoint_mul_single (s t : WithConv (MonoidAlgebra K M →ₐ[K] K)) (χ : M) :
    (s * t).ofConv (MonoidAlgebra.single χ 1) =
      s.ofConv (MonoidAlgebra.single χ 1) * t.ofConv (MonoidAlgebra.single χ 1) :=
  MonoidAlgebra.convMul_algHom_single_one s t χ

/-- A point evaluates a coordinate function through its character values. -/
theorem torusPoint_apply_eq_sum (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (F : MonoidAlgebra K M) :
    t.ofConv F = ∑ m ∈ F.coeff.support,
      F.coeff m * t.ofConv (MonoidAlgebra.single m 1) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single F]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : (MonoidAlgebra.single m (F.coeff m) : MonoidAlgebra K M) =
      F.coeff m • MonoidAlgebra.single m 1 := by
    rw [MonoidAlgebra.smul_single', mul_one]
  rw [h, map_smul, smul_eq_mul]

/-- The value of a torus point on a finite product of integral powers of
characters is the corresponding product of values. -/
theorem torusPoint_apply_prod_zpow (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    {S : Type*} [Fintype S] (χ : S → M) (m : S → ℤ) :
    t.ofConv (MonoidAlgebra.single (∏ s, χ s ^ m s) 1) =
      ∏ s, t.ofConv (MonoidAlgebra.single (χ s) 1) ^ m s := by
  let φ : M →* K := (t.ofConv : MonoidAlgebra K M →* K).comp (MonoidAlgebra.of K M)
  have hφ (x : M) : φ x = t.ofConv (MonoidAlgebra.single x 1) := rfl
  have hinv (x : M) : φ x⁻¹ = (φ x)⁻¹ := by
    rw [hφ, hφ, torusPoint_character_inv]
  rw [← hφ, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_zpow' φ hinv, hφ]

variable [Finite ι] [IsAlgClosed K]

/-- **Point-multiplicative coordinate functions are characters.** A nonzero
function on the split torus whose value at a convolution product of points is
the product of its values agrees at every point with one character. -/
theorem BorelTorusUnipotentCharacters.exists_of_torusPoint_multiplicative
    (F : MonoidAlgebra K M) (hF : F ≠ 0)
    (hmul : ∀ s t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      (s * t).ofConv F = s.ofConv F * t.ofConv F) :
    ∃ χ : M, ∀ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      t.ofConv F = t.ofConv (MonoidAlgebra.single χ 1) := by
  classical
  have hsupp : F.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hF (MonoidAlgebra.coeff_eq_zero.mp h)
  obtain ⟨χ, hχ⟩ := hsupp
  refine ⟨χ, fun s => ?_⟩
  let G : MonoidAlgebra K M := ∑ m ∈ F.coeff.support, MonoidAlgebra.single m
    (F.coeff m * (s.ofConv (MonoidAlgebra.single m 1) - s.ofConv F))
  have hG : G = 0 := by
    have hfin : Algebra.FiniteType K (MonoidAlgebra K M) := by
      have hfg : Monoid.FG M :=
        Group.fg_iff_monoid_fg.mp (AddGroup.fg_iff_mul_fg.mp
          (Module.Finite.iff_addGroup_fg.mp inferInstance))
      exact @MonoidAlgebra.finiteType_of_fg K M _ _ hfg
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (A := MonoidAlgebra K M) (K := K)
    intro f
    rw [map_zero]
    have hsingle (m : M) (c : K) : f (MonoidAlgebra.single m c) =
        c * f (MonoidAlgebra.single m 1) := by
      have h : (MonoidAlgebra.single m c : MonoidAlgebra K M) =
          c • MonoidAlgebra.single m 1 := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [h, map_smul, smul_eq_mul]
    have hst := hmul s (toConv f)
    rw [torusPoint_apply_eq_sum (s * toConv f) F, torusPoint_apply_eq_sum (toConv f) F] at hst
    simp only [torusPoint_mul_single] at hst
    have hGf : f G = ∑ m ∈ F.coeff.support,
        F.coeff m * (s.ofConv (MonoidAlgebra.single m 1) - s.ofConv F) *
          f (MonoidAlgebra.single m 1) := by
      simp only [G, map_sum]
      exact Finset.sum_congr rfl fun m _ => hsingle m _
    rw [hGf]
    have hexp : ∀ m ∈ F.coeff.support,
        F.coeff m * (s.ofConv (MonoidAlgebra.single m 1) - s.ofConv F) *
            f (MonoidAlgebra.single m 1) =
          F.coeff m * (s.ofConv (MonoidAlgebra.single m 1) * f (MonoidAlgebra.single m 1)) -
            s.ofConv F * (F.coeff m * f (MonoidAlgebra.single m 1)) := by
      intro m _
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.mul_sum, hst, sub_self]
  have hcoeff : G.coeff χ = F.coeff χ * (s.ofConv (MonoidAlgebra.single χ 1) - s.ofConv F) := by
    simp only [G, MonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single χ]
    · simp
    · intro m _ hm
      simp [hm]
    · intro h
      exact absurd hχ h
  rw [hG, MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
  have hne : F.coeff χ ≠ 0 := Finsupp.mem_support_iff.mp hχ
  have hsub := (mul_eq_zero.mp hcoeff.symm).resolve_left hne
  exact (sub_eq_zero.mp hsub).symm

omit [Finite ι] in
/-- In an algebraically closed field every unit has an `n`-th root for every
nonzero integer `n`. -/
private theorem units_zpow_surjective' {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun u : Kˣ => u ^ n) := by
  intro u
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact u.ne_zero hz.symm
  let v := Units.mk0 z hz0
  have hv : v ^ n.natAbs = u := Units.ext (by simp [v, hz])
  rcases Int.natAbs_eq n with h | h
  · refine ⟨v, ?_⟩
    change v ^ n = u
    rw [h, zpow_natCast, hv]
  · refine ⟨v⁻¹, ?_⟩
    change v⁻¹ ^ n = u
    rw [h, zpow_neg, zpow_natCast, inv_pow, inv_inv, hv]

omit [Finite ι] in
/-- **Prescribed character values under relations.** For an arbitrary finite
family of characters `χ` of the split torus and units `c` satisfying every
integral monomial relation among the `χ`, some `K`-point of the torus takes
the value `c s` at `χ s` for every `s`. -/
theorem BorelTorusUnipotentCharacters.exists_character_values_of_relations
    {S : Type*} [Fintype S] (χ : S → M) (c : S → Kˣ)
    (hrel : ∀ m : S → ℤ, ∏ s, χ s ^ m s = 1 → ∏ s, c s ^ m s = 1) :
    ∃ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      ∀ s, t.ofConv (MonoidAlgebra.single (χ s) 1) = c s := by
  classical
  let _ : DivisibleBy (Additive Kˣ) ℤ :=
    divisibleByOfSMulRightSurj (Additive Kˣ) ℤ (fun {n} hn a => by
      obtain ⟨v, hv⟩ := units_zpow_surjective' (K := K) hn (Additive.toMul a)
      exact ⟨Additive.ofMul v, by
        change n • Additive.ofMul v = a
        rw [← ofMul_zpow]
        exact congrArg Additive.ofMul hv⟩)
  let ψ : (S → ℤ) →ₗ[ℤ] (ι →₀ ℤ) :=
    Fintype.linearCombination ℤ (fun s => Multiplicative.toAdd (χ s))
  let φ : (S → ℤ) →ₗ[ℤ] Additive Kˣ :=
    Fintype.linearCombination ℤ (fun s => Additive.ofMul (c s))
  have hψ (m : S → ℤ) : ψ m = Multiplicative.toAdd (∏ s, χ s ^ m s) := by
    simp [ψ, Fintype.linearCombination_apply, toAdd_prod, toAdd_zpow]
  have hφ (m : S → ℤ) : φ m = Additive.ofMul (∏ s, c s ^ m s) := by
    simp [φ, Fintype.linearCombination_apply, ofMul_prod, ofMul_zpow]
  have hle : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro m hm
    rw [LinearMap.mem_ker] at hm ⊢
    rw [hψ] at hm
    have h1 : ∏ s, χ s ^ m s = 1 := Multiplicative.toAdd.injective (by rw [hm]; rfl)
    rw [hφ, hrel m h1, ofMul_one]
  let i := (LinearMap.ker ψ).liftQ ψ le_rfl
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  let g := (LinearMap.ker ψ).liftQ φ hle
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Kˣ)).extension_property i hi g
  let e : M →* K :=
    { toFun := fun m => ((Additive.toMul (h (Multiplicative.toAdd m)) : Kˣ) : K)
      map_one' := by simp
      map_mul' := by intro a b; simp }
  refine ⟨toConv (MonoidAlgebra.lift K K M e), fun s => ?_⟩
  change MonoidAlgebra.lift K K M e (MonoidAlgebra.single (χ s) 1) = c s
  rw [MonoidAlgebra.lift_single, one_smul]
  have hs : h (Multiplicative.toAdd (χ s)) = Additive.ofMul (c s) := by
    have hc := LinearMap.congr_fun hh ((LinearMap.ker ψ).mkQ (Pi.single s 1))
    simp only [LinearMap.comp_apply, i, g, Submodule.mkQ_apply, Submodule.liftQ_apply] at hc
    have hψs : ψ (Pi.single s 1) = Multiplicative.toAdd (χ s) := by
      simp [ψ, Fintype.linearCombination_apply, Pi.single_apply]
    have hφs : φ (Pi.single s 1) = Additive.ofMul (c s) := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    rw [hψs, hφs] at hc
    exact hc
  change ((Additive.toMul (h (Multiplicative.toAdd (χ s))) : Kˣ) : K) = c s
  rw [hs]
  rfl

end TorusUnipotent
