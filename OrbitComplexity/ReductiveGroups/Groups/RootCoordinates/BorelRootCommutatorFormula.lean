import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCommutator
import OrbitComplexity.ReductiveGroups.Geometry.DiagonalPolynomialWeights
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Borel Root Commutator Formula

The Chevalley commutator formula for the
Borel root subgroups. -/

noncomputable section
namespace ReductiveGroups

open TauCeti MvPolynomial

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
private theorem gaParameterPoint_neg (x : B →ₐc[K] SymmetricAlgebra K K) (u : K) :
    gaParameterPoint x (-u) = (gaParameterPoint x u)⁻¹ := by
  simp only [gaParameterPoint, ofAdd_neg, map_inv]

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
private theorem gaParameterPoint_zero' (x : B →ₐc[K] SymmetricAlgebra K K) :
    gaParameterPoint x (0 : K) = 1 := by
  simp only [gaParameterPoint, ofAdd_zero, map_one]

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
private theorem splitTorus_point_finsupp_prod''
    {κ : Type*} (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (χ : κ → M) (m : κ →₀ ℕ) :
    t.ofConv (MonoidAlgebra.single (m.prod fun j e => χ j ^ e) 1) =
      m.prod fun j e => t.ofConv (MonoidAlgebra.single (χ j) 1) ^ e := by
  let φ : M →* K := t.ofConv.toMonoidHom.comp (MonoidAlgebra.of K M)
  change φ (m.prod fun j e => χ j ^ e) = m.prod fun j e => φ (χ j) ^ e
  rw [map_finsuppProd]
  simp only [map_pow]

/-- The four-factor family `x_τ, x_β, x_τ, x_β` of a commutator. -/
private def commutatorFamily {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (τ β : borelRootCharacterIndex J π) : Fin 4 → B →ₐc[K] SymmetricAlgebra K K :=
  ![x τ, x β, x τ, x β]

private def commutatorCharacters {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    (τ β : borelRootCharacterIndex J π) : Fin 4 → M :=
  ![τ.val, β.val, τ.val, β.val]

private def commutatorParams (u t : K) : Fin 4 → K := ![u, t, -u, -t]

omit [IsAlgClosed K] [CharZero K] [Finite ι] in
private theorem commutator_list_prod {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (τ β : borelRootCharacterIndex J π) (u t : K) :
    (([0, 1, 2, 3] : List (Fin 4)).map fun k =>
        gaParameterPoint (commutatorFamily x τ β k) (commutatorParams u t k)).prod =
      gaParameterPoint (x τ) u * gaParameterPoint (x β) t *
        (gaParameterPoint (x τ) u)⁻¹ * (gaParameterPoint (x β) t)⁻¹ := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    commutatorFamily, commutatorParams, Matrix.cons_val, gaParameterPoint_neg, mul_assoc]

/-- The pulled-back logarithm coordinate of the commutator, as a polynomial
in the two parameters, has only monomials `u^a t^b` with `τ^a β^b = k`. -/
private theorem commutator_logPoly_monomial
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    (τ β k : borelRootCharacterIndex J π)
    (hyU : ∀ n, gaAffineGroupTangent (commutatorFamily x τ β n) ∈ rootTangentSpace J π hπ) :
    let q : MvPolynomial (Fin 2) K :=
      aeval (![X 0, X 1, -X 0, -X 1] : Fin 4 → MvPolynomial (Fin 2) K)
        (borelRootProductLogarithm J hJ π hπ (commutatorFamily x τ β) [0, 1, 2, 3] (e.coord k))
    (∀ v : Fin 2 → K, eval v q = aeval (commutatorParams (v 0) (v 1))
        (borelRootProductLogarithm J hJ π hπ (commutatorFamily x τ β) [0, 1, 2, 3]
          (e.coord k))) ∧
      ∀ m ∈ q.support, τ.val ^ m 0 * β.val ^ m 1 = k.val := by
  intro q
  have heval (v : Fin 2 → K) : eval v q = aeval (commutatorParams (v 0) (v 1))
      (borelRootProductLogarithm J hJ π hπ (commutatorFamily x τ β) [0, 1, 2, 3]
        (e.coord k)) := by
    change aeval v (aeval _ _) = _
    rw [comp_aeval_apply]
    have hfun : (fun n => aeval v ((![X 0, X 1, -X 0, -X 1] : Fin 4 → MvPolynomial (Fin 2) K) n)) =
        commutatorParams (v 0) (v 1) := by
      funext n
      fin_cases n <;> simp [commutatorParams]
    rw [hfun]
  refine ⟨heval, ?_⟩
  have hew (i) : (e i).val ∈ affineGroupCharacterWeightSpace π i.val := by
    rw [he]; exact hx i
  have hcov : ∀ (t0 : WithConv (MonoidAlgebra K M →ₐ[K] K)) (v : Fin 2 → K),
      eval (fun n => (![t0.ofConv (MonoidAlgebra.single τ.val 1),
        t0.ofConv (MonoidAlgebra.single β.val 1)] : Fin 2 → K) n * v n) q =
        t0.ofConv (MonoidAlgebra.single k.val 1) * eval v q := by
    intro t0 v
    rw [heval, heval]
    have hfun : commutatorParams
        ((![t0.ofConv (MonoidAlgebra.single τ.val 1),
          t0.ofConv (MonoidAlgebra.single β.val 1)] : Fin 2 → K) 0 * v 0)
        ((![t0.ofConv (MonoidAlgebra.single τ.val 1),
          t0.ofConv (MonoidAlgebra.single β.val 1)] : Fin 2 → K) 1 * v 1) =
        fun n => t0.ofConv (MonoidAlgebra.single (commutatorCharacters τ β n) 1) *
          commutatorParams (v 0) (v 1) n := by
      funext n
      fin_cases n <;> simp [commutatorParams, commutatorCharacters]
    rw [hfun]
    exact BorelRootProductLogarithm.diagonal_equivariant J hJ π hπ (commutatorFamily x τ β) hyU
      [0, 1, 2, 3] (e.coord k) (AlgHom.mapDomain π t0)
      (borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t0)
      (fun n => t0.ofConv (MonoidAlgebra.single (commutatorCharacters τ β n) 1))
      (t0.ofConv (MonoidAlgebra.single k.val 1))
      (fun n => by
        fin_cases n <;>
        exact AffineGroupAdjoint.eq_character_of_mem_weight π _ t0 _ (hx _))
      (fun d => borelRootCoordinateBasis_coord_torus_ad I J hJI hI hJ π hπ hker hB
        e hew t0 k d) (commutatorParams (v 0) (v 1))
  intro m hm
  apply splitTorus_character_eq_of_point_eval_eq (K := K) (ν := ι)
  intro t0
  have hmc := DiagonalPolynomialWeights.character_of_diagonal_equivariant q
    (fun (n : Fin 2) (t0 : WithConv (MonoidAlgebra K M →ₐ[K] K)) =>
      (![t0.ofConv (MonoidAlgebra.single τ.val 1),
        t0.ofConv (MonoidAlgebra.single β.val 1)] : Fin 2 → K) n)
    (fun t0 => t0.ofConv (MonoidAlgebra.single k.val 1)) hcov m hm t0
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two] at hmc
  have hsplit : t0.ofConv (MonoidAlgebra.single (τ.val ^ m 0 * β.val ^ m 1) 1) =
      t0.ofConv (MonoidAlgebra.single τ.val 1) ^ m 0 *
        t0.ofConv (MonoidAlgebra.single β.val 1) ^ m 1 := by
    let φ : M →* K := t0.ofConv.toMonoidHom.comp (MonoidAlgebra.of K M)
    change φ (τ.val ^ m 0 * β.val ^ m 1) = φ τ.val ^ m 0 * φ β.val ^ m 1
    rw [map_mul, map_pow, map_pow]
  rw [hsplit]
  simpa using hmc

/-- **Chevalley commutator formula**. For
distinct Borel root characters `τ ≠ β` (positive roots),
root Ga points `x`, and any duplicate-free list of the positive roots
`iτ + jβ` with `i, j > 0`, there are constants such that
`x_τ(u) x_β(t) = (∏ x_{iτ+jβ}(c u^i t^j)) x_β(t) x_τ(u)` for all `u, t`. -/
theorem borelRoot_commutator_formula
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    {τ β : borelRootCharacterIndex J π} (hτβ : τ ≠ β)
    (l : List (commutatorRootSet τ β)) (hl : l.Nodup) (hall : ∀ γ, γ ∈ l) :
    ∃ (i j : commutatorRootSet τ β → ℕ) (c : commutatorRootSet τ β → K),
      (∀ γ, 0 < i γ ∧ 0 < j γ ∧ γ.val.val = τ.val ^ i γ * β.val ^ j γ) ∧
      ∀ u t : K, gaParameterPoint (x τ) u * gaParameterPoint (x β) t =
        (l.map fun γ => gaParameterPoint (x γ.val) (c γ * u ^ i γ * t ^ j γ)).prod *
          gaParameterPoint (x β) t * gaParameterPoint (x τ) u := by
  classical
  have hSet := commutatorRootSet_closed τ β
  choose i j hi hj hij using (fun γ : commutatorRootSet τ β => γ.property)
  have hxU (k) : gaAffineGroupTangent (x k) ∈ rootTangentSpace J π hπ :=
    he k ▸ (e k).property
  let E := borelRootUnipotentExponentialEquiv J hJ π hπ
  have hyU : ∀ n, gaAffineGroupTangent (commutatorFamily x τ β n) ∈ rootTangentSpace J π hπ := by
    intro n; fin_cases n <;> exact hxU _
  have hy : ∀ n, gaAffineGroupTangent (commutatorFamily x τ β n) ∈
      affineGroupCharacterWeightSpace π (commutatorCharacters τ β n) := by
    intro n; fin_cases n <;> exact hx _
  have hew (k) : (e k).val ∈ affineGroupCharacterWeightSpace π k.val := by
    rw [he]; exact hx k
  let gpt : K → K → borelRootUnipotentPoints J π hπ := fun u t =>
    ⟨_, GaParameterPoint.prod_mem_of_tangent_mem_quotient (commutatorFamily x τ β)
      (borelRootUnipotentHopfIdeal J π hπ) hyU [0, 1, 2, 3] (commutatorParams u t)⟩
  have hgval (u t : K) : (gpt u t).val = gaParameterPoint (x τ) u * gaParameterPoint (x β) t *
      (gaParameterPoint (x τ) u)⁻¹ * (gaParameterPoint (x β) t)⁻¹ :=
    commutator_list_prod x τ β u t
  have hgone₁ (u : K) : gpt u 0 = 1 := by
    apply Subtype.ext
    rw [hgval, gaParameterPoint_zero']
    simp
  have hgone₂ (t : K) : gpt 0 t = 1 := by
    apply Subtype.ext
    rw [hgval, gaParameterPoint_zero']
    simp
  have hcoordEval (u t : K) (k : borelRootCharacterIndex J π) :
      e.coord k (E.symm (gpt u t)) = aeval (commutatorParams u t)
        (borelRootProductLogarithm J hJ π hπ (commutatorFamily x τ β) [0, 1, 2, 3]
          (e.coord k)) :=
    (borelRootProductLogarithm_eval J hJ π hπ (commutatorFamily x τ β) hyU
      [0, 1, 2, 3] (e.coord k) (commutatorParams u t)).symm
  -- Step 1: the logarithm of the commutator has no coordinates outside the set.
  have hlog : ∀ u t, gpt u t ∈ borelRootSubsetPoints J hJ π hπ e (commutatorRootSet τ β) := by
    intro u t k hk
    by_cases hmono : ∃ a b : ℕ, k.val = τ.val ^ a * β.val ^ b
    · obtain ⟨a, b, hab⟩ := hmono
      have hab0 : a = 0 ∨ b = 0 := by
        by_contra hne
        push Not at hne
        exact hk ⟨a, b, Nat.pos_of_ne_zero hne.1, Nat.pos_of_ne_zero hne.2, hab⟩
      obtain ⟨hmain, hmonoq⟩ := commutator_logPoly_monomial I J hJI hI hJ π hπ hker hB
        x e he hx τ β k hyU
      set q := aeval (![X 0, X 1, -X 0, -X 1] : Fin 4 → MvPolynomial (Fin 2) K)
        (borelRootProductLogarithm J hJ π hπ (commutatorFamily x τ β) [0, 1, 2, 3]
          (e.coord k)) with hqdef
      -- `k` is `τ` or `β`, and then `q` is a multiple of one variable.
      have hkτβ : k = τ ∨ k = β := by
        rcases hab0 with ha | hb
        · right
          by_contra hkβ
          have hlin := BorelRootCharacter.pair_linearIndependent I J hJI hI hJ π hπ hker hB hkβ
          rw [LinearIndependent.pair_iff] at hlin
          have hrel : (1 : ℤ) • Multiplicative.toAdd k.val +
              (-(b : ℤ)) • Multiplicative.toAdd β.val = 0 := by
            rw [hab, ha, pow_zero, one_mul, toAdd_pow, one_smul, neg_smul, natCast_zsmul,
              add_neg_cancel]
          exact one_ne_zero (hlin _ _ hrel).1
        · left
          by_contra hkτ
          have hlin := BorelRootCharacter.pair_linearIndependent I J hJI hI hJ π hπ hker hB hkτ
          rw [LinearIndependent.pair_iff] at hlin
          have hrel : (1 : ℤ) • Multiplicative.toAdd k.val +
              (-(a : ℤ)) • Multiplicative.toAdd τ.val = 0 := by
            rw [hab, hb, pow_zero, mul_one, toAdd_pow, one_smul, neg_smul, natCast_zsmul,
              add_neg_cancel]
          exact one_ne_zero (hlin _ _ hrel).1
      have hq0 : q = 0 := by
        rcases hkτβ with rfl | rfl
        · have hsupp : ∀ m ∈ q.support, m = Finsupp.single 0 1 := by
            intro m hm
            have h := hmonoq m hm
            have h' : k.val ^ m 0 * β.val ^ m 1 = k.val ^ 1 * β.val ^ 0 := by
              rw [h, pow_one, pow_zero, mul_one]
            obtain ⟨h0, h1⟩ :=
              borelRootCharacter_pow_mul_pow_inj I J hJI hI hJ π hπ hker hB hτβ h'
            ext n; fin_cases n <;> simp [h0, h1]
          have hκ : q.coeff (Finsupp.single 0 1) = 0 := by
            have hv := hmain ![1, 0]
            have hq : q = C (q.coeff (Finsupp.single 0 1)) * X 0 := by
              ext m
              by_cases hm : m = Finsupp.single 0 1
              · subst hm; simp [coeff_C_mul, coeff_X]
              · rw [coeff_C_mul, coeff_X, ite_eq_right (Ne.symm hm), mul_zero]
                exact MvPolynomial.notMem_support_iff.mp (fun h => hm (hsupp m h))
            rw [hq] at hv
            simp only [map_mul, eval_C, eval_X, Matrix.cons_val_zero, mul_one] at hv
            rw [hv, ← hcoordEval]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [hgone₁, BorelRootUnipotentExponentialEquiv.symm_one, map_zero]
          ext m
          by_cases hm : m ∈ q.support
          · rw [hsupp m hm, hκ, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
          · rw [MvPolynomial.notMem_support_iff.mp hm, AddMonoidAlgebra.coeff_zero,
              Finsupp.coe_zero, Pi.zero_apply]
        · have hsupp : ∀ m ∈ q.support, m = Finsupp.single 1 1 := by
            intro m hm
            have h := hmonoq m hm
            have h' : τ.val ^ m 0 * k.val ^ m 1 = τ.val ^ 0 * k.val ^ 1 := by
              rw [h, pow_one, pow_zero, one_mul]
            obtain ⟨h0, h1⟩ :=
              borelRootCharacter_pow_mul_pow_inj I J hJI hI hJ π hπ hker hB hτβ h'
            ext n; fin_cases n <;> simp [h0, h1]
          have hκ : q.coeff (Finsupp.single 1 1) = 0 := by
            have hv := hmain ![0, 1]
            have hq : q = C (q.coeff (Finsupp.single 1 1)) * X 1 := by
              ext m
              by_cases hm : m = Finsupp.single 1 1
              · subst hm; simp [coeff_C_mul, coeff_X]
              · rw [coeff_C_mul, coeff_X, ite_eq_right (Ne.symm hm), mul_zero]
                exact MvPolynomial.notMem_support_iff.mp (fun h => hm (hsupp m h))
            rw [hq] at hv
            simp only [map_mul, eval_C, eval_X, Matrix.cons_val_one, Matrix.cons_val_zero,
              mul_one] at hv
            rw [hv, ← hcoordEval]
            rw [hgone₂, BorelRootUnipotentExponentialEquiv.symm_one, map_zero]
          ext m
          by_cases hm : m ∈ q.support
          · rw [hsupp m hm, hκ, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
          · rw [MvPolynomial.notMem_support_iff.mp hm, AddMonoidAlgebra.coeff_zero,
              Finsupp.coe_zero, Pi.zero_apply]
      have hv := hmain ![u, t]
      rw [hq0, map_zero] at hv
      rw [hcoordEval]
      exact hv.symm
    · rw [hcoordEval, BorelRootProductLogarithm.eq_zero_of_not_monomial I J hJI hI hJ π hπ
        hker hB e hew (commutatorFamily x τ β) (commutatorCharacters τ β) hy hyU
        [0, 1, 2, 3] k _, map_zero]
      intro m hm
      apply hmono
      refine ⟨m 0 + m 2, m 1 + m 3, ?_⟩
      rw [← hm, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
      simp only [commutatorCharacters, Matrix.cons_val]
      rw [pow_add, pow_add]
      simp only [mul_comm, mul_left_comm, mul_assoc]
  -- Step 2: the chart of the closed set, and torus rescaling.
  obtain ⟨c, hc⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
    x e he hx hxU hSet l hl hall (gpt 1 1) (hlog 1 1)
  refine ⟨i, j, c, fun γ => ⟨hi γ, hj γ, hij γ⟩, ?_⟩
  intro u t
  have hprod : (l.map fun γ => gaParameterPoint (x γ.val) (c γ * u ^ i γ * t ^ j γ)).prod =
      gaParameterPoint (x τ) u * gaParameterPoint (x β) t *
        (gaParameterPoint (x τ) u)⁻¹ * (gaParameterPoint (x β) t)⁻¹ := by
    by_cases hut : u ≠ 0 ∧ t ≠ 0
    · obtain ⟨t0, ht0τ, ht0β⟩ := exists_torusPoint_pair_values I J hJI hI hJ π hπ hker hB
        hτβ u t hut.1 hut.2
      have hval (γ : commutatorRootSet τ β) :
          c γ * u ^ i γ * t ^ j γ = t0.ofConv (MonoidAlgebra.single γ.val.val 1) * c γ := by
        let φ : M →* K := t0.ofConv.toMonoidHom.comp (MonoidAlgebra.of K M)
        have hφ : t0.ofConv (MonoidAlgebra.single γ.val.val 1) = u ^ i γ * t ^ j γ := by
          change φ γ.val.val = _
          rw [hij γ, map_mul, map_pow, map_pow]
          change t0.ofConv (MonoidAlgebra.single τ.val 1) ^ i γ *
            t0.ofConv (MonoidAlgebra.single β.val 1) ^ j γ = _
          rw [ht0τ, ht0β]
        rw [hφ]; ring
      have hconj := borelRootSubsetProduct_torus_conj J π hπ x hxU hx
        (commutatorRootSet τ β) l c t0
      rw [hc] at hconj
      have hlist : (l.map fun γ => gaParameterPoint (x γ.val) (c γ * u ^ i γ * t ^ j γ)).prod =
          (borelRootSubsetProduct J π hπ x hxU (commutatorRootSet τ β) l
            (fun γ => t0.ofConv (MonoidAlgebra.single γ.val.val 1) * c γ)).val := by
        change _ = (l.map fun γ => gaParameterPoint (x γ.val)
          (t0.ofConv (MonoidAlgebra.single γ.val.val 1) * c γ)).prod
        congr 1
        apply List.map_congr_left
        intro γ _
        rw [hval]
      rw [hlist, ← hconj, hgval]
      have hfac (k : borelRootCharacterIndex J π) (s : K) :
          AlgHom.mapDomain π t0 * gaParameterPoint (x k) s * (AlgHom.mapDomain π t0)⁻¹ =
            gaParameterPoint (x k) (t0.ofConv (MonoidAlgebra.single k.val 1) * s) :=
        GaAffineGroupPoints.conjugate_of_tangent_eq (x k) (x k) (AlgHom.mapDomain π t0) _
          (AffineGroupAdjoint.eq_character_of_mem_weight π k.val t0 _ (hx k)) s
      have hτ' : AlgHom.mapDomain π t0 * gaParameterPoint (x τ) 1 *
          (AlgHom.mapDomain π t0)⁻¹ = gaParameterPoint (x τ) u := by
        rw [hfac, ht0τ, mul_one]
      have hβ' : AlgHom.mapDomain π t0 * gaParameterPoint (x β) 1 *
          (AlgHom.mapDomain π t0)⁻¹ = gaParameterPoint (x β) t := by
        rw [hfac, ht0β, mul_one]
      rw [← hτ', ← hβ']
      group
    · have hzero : ∀ γ : commutatorRootSet τ β, c γ * u ^ i γ * t ^ j γ = 0 := by
        intro γ
        rcases not_and_or.mp hut with hu | ht
        · rw [not_not.mp hu, zero_pow (hi γ).ne', mul_zero, zero_mul]
        · rw [not_not.mp ht, zero_pow (hj γ).ne', mul_zero]
      have hone : (l.map fun γ => gaParameterPoint (x γ.val) (c γ * u ^ i γ * t ^ j γ)).prod =
          1 := by
        apply List.prod_eq_one
        intro g hg
        obtain ⟨γ, -, rfl⟩ := List.mem_map.mp hg
        rw [hzero, gaParameterPoint_zero']
      rw [hone]
      rcases not_and_or.mp hut with hu | ht
      · rw [not_not.mp hu, gaParameterPoint_zero']; group
      · rw [not_not.mp ht, gaParameterPoint_zero']; group
  rw [hprod]
  group

end ReductiveGroups
