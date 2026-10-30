import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Complex.Polynomial.Basic
import OrbitComplexity.GroupActions.Tori.MonomialMaps
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Setoid.Basic
import Batteries.Tactic.Lint

/-! # Extension of characters

The units of an algebraically closed field are divisible. Baer's criterion over the integers
therefore extends a character of any additive subgroup to its ambient abelian group.
Equal-weight binomial relations descend integer exponent values to the weight subgroup, giving
one ambient character. Homogeneous weights separate a common scalar from a torus character.
-/

namespace GroupActions

noncomputable section

open Multiplicative

universe u v w

/-- A surjective invariant classifies a setoid quotient when equality of invariant values
is exactly the equivalence relation. -/
theorem exists_quotient_equiv {X : Type u} {Y : Type v}
    (r : Setoid X) (f : X → Y) (hsurj : Function.Surjective f)
    (hker : ∀ a b, f a = f b ↔ r a b) :
    ∃ e : Quotient r ≃ Y, ∀ x, e (Quotient.mk r x) = f x := by
  let g : Quotient r → Y := Quotient.lift f (fun a b h ↦ (hker a b).mpr h)
  have hinj : Function.Injective g := by
    intro q q' h
    revert h
    refine Quotient.inductionOn₂ q q' ?_
    intro a b hab
    exact Quotient.sound ((hker a b).mp hab)
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Quotient.mk r x, rfl⟩
  exact ⟨Equiv.ofBijective g ⟨hinj, hgsurj⟩, fun _ ↦ rfl⟩


private theorem weight_embDomain {A : Type u} {B : Type v} {M : Type w}
    [Fintype A] [Fintype B] [AddCommGroup M] (χ : B → M) (f : A ↪ B) (d : A → ℕ) :
    weightMonoidHom χ
        (ofAdd (((Finsupp.equivFunOnFinite.symm d).embDomain f : B →₀ ℕ) : B → ℕ)) =
      weightMonoidHom (fun i ↦ χ (f i)) (ofAdd d) := by
  classical
  change ofAdd (Fintype.linearCombination ℕ χ _) =
    ofAdd (Fintype.linearCombination ℕ (fun i ↦ χ (f i)) d)
  simp only [Fintype.linearCombination_apply]
  congr 1
  calc
    _ = ((Finsupp.equivFunOnFinite.symm d).embDomain f).sum (fun b n ↦ n • χ b) :=
      (Finsupp.sum_fintype ((Finsupp.equivFunOnFinite.symm d).embDomain f)
        (fun b (n : ℕ) ↦ n • χ b) (fun b ↦ zero_smul ℕ (χ b))).symm
    _ = (Finsupp.equivFunOnFinite.symm d).sum (fun a n ↦ n • χ (f a)) :=
      Finsupp.sum_embDomain
    _ = _ := by simp [Finsupp.sum_fintype]

private theorem product_embDomain {A : Type u} {B : Type v} {K : Type w}
    [Fintype A] [Fintype B] [CommMonoid K] (z : B → K) (f : A ↪ B) (d : A → ℕ) :
    ∏ b, z b ^ ((Finsupp.equivFunOnFinite.symm d).embDomain f b) =
      ∏ a, z (f a) ^ d a := by
  classical
  calc
    _ = ((Finsupp.equivFunOnFinite.symm d).embDomain f).prod (fun b n ↦ z b ^ n) :=
      (Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _).symm
    _ = (Finsupp.equivFunOnFinite.symm d).prod (fun a n ↦ z (f a) ^ n) :=
      Finsupp.prod_embDomain
    _ = _ := by simp [Finsupp.prod_fintype]

/-- Binomial relations restrict along a finite embedding with the recorded weight identity. -/
theorem binomial_relations_restrict {A : Type u} {B : Type v} {M K : Type w}
    [Fintype A] [Fintype B] [AddCommGroup M] [CommMonoid K]
    (χ : B → M) (z : B → K)
    (hrel : ∀ d e : B → ℕ, weightMonoidHom χ (ofAdd d) = weightMonoidHom χ (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i) (f : A ↪ B)
    (ψ : A → M) (hψ : ∀ i, χ (f i) = ψ i) :
    ∀ d e : A → ℕ,
      weightMonoidHom ψ (ofAdd d) = weightMonoidHom ψ (ofAdd e) →
      ∏ i, z (f i) ^ d i = ∏ i, z (f i) ^ e i := by
  classical
  intro d e hde
  let D : B →₀ ℕ := (Finsupp.equivFunOnFinite.symm d).embDomain f
  let E : B →₀ ℕ := (Finsupp.equivFunOnFinite.symm e).embDomain f
  have hχ : (fun i ↦ χ (f i)) = ψ := funext hψ
  have ht := hrel D E (by rw [weight_embDomain, weight_embDomain, hχ]; exact hde)
  simpa only [D, E, product_embDomain] using ht

/-- Coordinate quotients of binomial solutions satisfy the same weight relations. -/
theorem binomial_relations_div {A : Type u} {M K : Type v}
    [Fintype A] [AddCommGroup M] [Field K] (χ : A → M) (x y : A → K)
    (hx : ∀ d e : A → ℕ, weightMonoidHom χ (ofAdd d) = weightMonoidHom χ (ofAdd e) →
      ∏ i, x i ^ d i = ∏ i, x i ^ e i)
    (hy : ∀ d e : A → ℕ, weightMonoidHom χ (ofAdd d) = weightMonoidHom χ (ofAdd e) →
      ∏ i, y i ^ d i = ∏ i, y i ^ e i) :
    ∀ d e : A → ℕ, weightMonoidHom χ (ofAdd d) = weightMonoidHom χ (ofAdd e) →
      ∏ i, (y i / x i) ^ d i = ∏ i, (y i / x i) ^ e i := by
  intro d e hde
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, hx d e hde, hy d e hde]

variable {K M : Type*} [Field K] [IsAlgClosed K]

/-- The units of an algebraically closed field are divisible by nonzero natural numbers. -/
instance unitsDivisibleNat : DivisibleBy (Additive Kˣ) ℕ := by
  apply divisibleByOfSMulRightSurj
  intro n hn a
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : K) (Nat.pos_of_ne_zero hn)
  have hzne : z ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn] at hz
    exact a.toMul.ne_zero hz.symm
  refine ⟨Additive.ofMul (Units.mk0 z hzne), ?_⟩
  apply Additive.ext
  rw [toMul_nsmul]
  apply Units.ext
  change z ^ n = (a.toMul : K)
  exact hz

/-- The units of an algebraically closed field are divisible by nonzero integers. -/
instance unitsDivisibleInt : DivisibleBy (Additive Kˣ) ℤ :=
  AddGroup.divisibleByIntOfDivisibleByNat (Additive Kˣ)

/-- A character of an additive subgroup extends to the whole abelian group. -/
theorem exists_character_extension [AddCommGroup M] (L : AddSubgroup M)
    (f : L →+ Additive Kˣ) :
    ∃ F : M →+ Additive Kˣ, F.comp L.subtype = f := by
  exact (Module.Baer.of_divisible (Additive Kˣ)).extension_property_addMonoidHom
    L.subtype Subtype.val_injective f

open scoped BigOperators

variable {I : Type*} [Fintype I] [AddCommGroup M]

private theorem linearCombination_natCast {A : Type*} [AddCommGroup A]
    (v : I → A) (d : I →₀ ℕ) :
    Finsupp.linearCombination ℤ v (d.mapRange Int.ofNat rfl) =
      Fintype.linearCombination ℕ v (d : I → ℕ) := by
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun i => zero_smul ℤ (v i)), Fintype.linearCombination_apply]
  simp only [Finsupp.mapRange_apply, Int.ofNat_eq_natCast, natCast_zsmul]

omit [IsAlgClosed K] in
private theorem relations_vanish (weights : I → M) (z : I → Kˣ)
    (hrel : ∀ d e : I → ℕ,
      weightMonoidHom weights (ofAdd d) = weightMonoidHom weights (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i)
    (n : I →₀ ℤ) (hn : Finsupp.linearCombination ℤ weights n = 0) :
    Finsupp.linearCombination ℤ (fun i => Additive.ofMul (z i)) n = 0 := by
  classical
  let d : I →₀ ℕ := n.mapRange Int.toNat rfl
  let e : I →₀ ℕ := n.mapRange (fun a => (-a).toNat) rfl
  have hsplit : n = d.mapRange Int.ofNat rfl - e.mapRange Int.ofNat rfl := by
    ext i
    change n i = ((n i).toNat : ℤ) - ((-n i).toNat : ℤ)
    exact (Int.toNat_sub_toNat_neg (n i)).symm
  have hweight : Fintype.linearCombination ℕ weights (d : I → ℕ) =
      Fintype.linearCombination ℕ weights (e : I → ℕ) := by
    rw [← linearCombination_natCast, ← linearCombination_natCast]
    apply sub_eq_zero.mp
    rw [← map_sub, ← hsplit]
    exact hn
  have hw : weightMonoidHom weights (ofAdd (d : I → ℕ)) =
      weightMonoidHom weights (ofAdd (e : I → ℕ)) :=
    congrArg ofAdd hweight
  have hprod := hrel (d : I → ℕ) (e : I → ℕ) hw
  have hz : Fintype.linearCombination ℕ (fun i => Additive.ofMul (z i)) (d : I → ℕ) =
      Fintype.linearCombination ℕ (fun i => Additive.ofMul (z i)) (e : I → ℕ) := by
    apply Additive.ext
    simpa only [Fintype.linearCombination_apply, toMul_sum, toMul_nsmul,
      toMul_ofMul] using hprod
  rw [hsplit, map_sub, linearCombination_natCast, linearCombination_natCast]
  exact sub_eq_zero.mpr hz

/-- Unit coordinates satisfying the weight relations are values of one lattice character. -/
theorem exists_character_of_relations (weights : I → M) (z : I → Kˣ)
    (hrel : ∀ d e : I → ℕ,
      weightMonoidHom weights (ofAdd d) = weightMonoidHom weights (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i) :
    ∃ τ : Multiplicative M →* Kˣ, ∀ i, τ (ofAdd (weights i)) = z i := by
  let W : (I →₀ ℤ) →+ M := (Finsupp.linearCombination ℤ weights).toAddMonoidHom
  let Z : (I →₀ ℤ) →+ Additive Kˣ :=
    (Finsupp.linearCombination ℤ (fun i => Additive.ofMul (z i))).toAddMonoidHom
  have hker : W.rangeRestrict.ker ≤ Z.ker := by
    intro n hn
    rw [AddMonoidHom.ker_rangeRestrict] at hn
    change W n = 0 at hn
    change Z n = 0
    exact relations_vanish weights z hrel n hn
  let f : W.range →+ Additive Kˣ :=
    W.rangeRestrict.liftOfSurjective W.rangeRestrict_surjective ⟨Z, hker⟩
  have hfactor : f.comp W.rangeRestrict = Z := by
    exact congrArg Subtype.val
      ((W.rangeRestrict.liftOfSurjective W.rangeRestrict_surjective).symm_apply_apply ⟨Z, hker⟩)
  obtain ⟨F, hF⟩ := exists_character_extension W.range f
  refine ⟨AddMonoidHom.toMultiplicativeLeft F, fun i => ?_⟩
  have hFsingle := DFunLike.congr_fun hF (W.rangeRestrict (Finsupp.single i 1))
  have hfactorSingle := DFunLike.congr_fun hfactor (Finsupp.single i 1)
  have hs : F (W (Finsupp.single i 1)) = Z (Finsupp.single i 1) :=
    hFsingle.trans hfactorSingle
  change F (Finsupp.linearCombination ℤ weights (Finsupp.single i 1)) =
    Finsupp.linearCombination ℤ (fun i => Additive.ofMul (z i)) (Finsupp.single i 1) at hs
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul,
    one_smul] at hs
  change (F (weights i)).toMul = z i
  simpa only [toMul_ofMul] using congrArg Additive.toMul hs

/-- Homogeneous weight relations determine a common scalar and a torus character. -/
theorem exists_homogeneous_character (weights : I → M) (z : I → Kˣ)
    (hrel : ∀ d e : I → ℕ,
      weightMonoidHom (fun i => ((1 : ℤ), weights i)) (ofAdd d) =
        weightMonoidHom (fun i => ((1 : ℤ), weights i)) (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i) :
    ∃ (s : Kˣ) (τ : Multiplicative M →* Kˣ), ∀ i, z i = s * τ (ofAdd (weights i)) := by
  obtain ⟨η, hη⟩ := exists_character_of_relations (fun i => ((1 : ℤ), weights i)) z hrel
  refine ⟨η (ofAdd ((1 : ℤ), (0 : M))),
    η.comp (AddMonoidHom.inr ℤ M).toMultiplicative, fun i => ?_⟩
  rw [← hη i]
  change η (ofAdd ((1 : ℤ), weights i)) =
    η (ofAdd ((1 : ℤ), (0 : M))) * η (ofAdd ((0 : ℤ), weights i))
  rw [← map_mul]
  congr 1
  change ((1 : ℤ), weights i) = ((1 : ℤ) + 0, (0 : M) + weights i)
  simp only [add_zero, zero_add]


end
end GroupActions
