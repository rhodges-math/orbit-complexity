import TauCeti.Algebra.MonoidAlgebra.Localization
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Tactic

/-! # Partial inversion of polynomial coordinates

Splitting selected exponents into integer and nonnegative coordinates describes localization
away from the product of the selected variables.
-/

noncomputable section
open scoped TensorProduct
namespace GroupActions
universe u v
variable {ι : Type v} [Finite ι]

private def splitExponent (S : Finset ι) :
    (ι →₀ ℕ) →+ ((S → ℤ) × ({j // j ∉ S} → ℕ)) where
  toFun a := (fun j => (a j : ℤ), fun j => a j)
  map_zero' := by ext j <;> rfl
  map_add' a b := by ext j <;> simp

private def denominator (S : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator S (fun _ _ => 1)

omit [Finite ι] in
private theorem split_injective (S : Finset ι) :
    Function.Injective (splitExponent S) := by
  intro a b h
  ext j
  by_cases hj : j ∈ S
  · have e := congrFun (congrArg Prod.fst h) ⟨j, hj⟩
    exact Int.ofNat_inj.mp e
  · exact congrFun (congrArg Prod.snd h) ⟨j, hj⟩

private theorem split_surj (S : Finset ι) (y : (S → ℤ) × ({j // j ∉ S} → ℕ)) :
    ∃ n : ℕ, y + n • splitExponent S (denominator S) ∈ Set.range (splitExponent S) := by
  classical
  let n : ℕ := ∑ j : S, (-y.1 j).toNat
  have hn (j : S) : 0 ≤ y.1 j + (n : ℤ) := by
    have hb : (-y.1 j).toNat ≤ n :=
      Finset.single_le_sum (f := fun k : S => (-y.1 k).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hc : (0 : ℤ) ≤ ((-y.1 j).toNat : ℤ) := Int.natCast_nonneg _
    by_cases hy : 0 ≤ -y.1 j
    · have he := Int.toNat_of_nonneg hy
      omega
    · omega
  let a : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun j => if h : j ∈ S then (y.1 ⟨j, h⟩ + (n : ℤ)).toNat else y.2 ⟨j, h⟩)
  refine ⟨n, a, ?_⟩
  apply Prod.ext
  · ext j
    change ((a j : ℕ) : ℤ) = y.1 j + (n • splitExponent S (denominator S)).1 j
    simp only [a, Finsupp.coe_equivFunOnFinite_symm, dite_eq_left j.property]
    rw [Int.toNat_of_nonneg (hn j)]
    simp [splitExponent, denominator]
  · ext j
    change a j = y.2 j + (n • splitExponent S (denominator S)).2 j
    simp [a, splitExponent, denominator, j.property]

omit [Finite ι] in
private theorem split_unit (S : Finset ι) :
    IsUnit ((splitExponent S).toMultiplicative (.ofAdd (denominator S))) := by
  classical
  refine ⟨⟨_, .ofAdd ((fun _ => (-1 : ℤ)), 0), ?_, ?_⟩, rfl⟩
  · change splitExponent S (denominator S) + ((fun _ => (-1 : ℤ)), 0) = 0
    ext j <;> simp [splitExponent, denominator, j.property]
  · change ((fun _ => (-1 : ℤ)), 0) + splitExponent S (denominator S) = 0
    ext j <;> simp [splitExponent, denominator, j.property]

private theorem mixed_localization (R : Type u) [CommRing R] (S : Finset ι) :
    let f := (splitExponent S).toMultiplicative
    letI := (MonoidAlgebra.mapDomainRingHom R f).toAlgebra
    IsLocalization.Away
      (MonoidAlgebra.single (Multiplicative.ofAdd (denominator S)) (1 : R))
      (MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ)))) := by
  apply TauCeti.MonoidAlgebra.isLocalization_away_mapDomainRingHom R
    (splitExponent S).toMultiplicative
  · intro a b h
    exact congrArg Multiplicative.ofAdd (split_injective S h)
  · exact split_unit S
  · intro y
    obtain ⟨n, a, ha⟩ := split_surj S y.toAdd
    exact ⟨n, .ofAdd a, ha⟩

private def polyEquiv (R : Type u) [CommRing R] :
    MvPolynomial ι R ≃ₐ[R] MonoidAlgebra R (Multiplicative (ι →₀ ℕ)) :=
  AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (ι →₀ ℕ)

private def mixedMap (R : Type u) [CommRing R] (S : Finset ι) :
    MvPolynomial ι R →ₐ[R]
      MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ))) :=
  (MonoidAlgebra.mapDomainAlgHom R R (splitExponent S).toMultiplicative).comp
    (polyEquiv R).toAlgHom

omit [Finite ι] in
private theorem product_denominator (R : Type u) [CommRing R] (S : Finset ι) :
    polyEquiv R (∏ j ∈ S, MvPolynomial.X j) =
      MonoidAlgebra.single (Multiplicative.ofAdd (denominator S)) (1 : R) := by
  classical
  have hd : (∑ j ∈ S, Finsupp.single j (1 : ℕ)) = denominator S := by
    ext j
    by_cases hj : j ∈ S <;> simp [denominator, Finsupp.single_apply, hj]
  change (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (ι →₀ ℕ))
    (∏ j ∈ S, AddMonoidAlgebra.single (Finsupp.single j 1) 1) = _
  rw [map_prod]
  simp only [
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.prod_single,
    Finset.prod_const_one]
  rw [← ofAdd_sum, hd]

private theorem polynomial_localization (R : Type u) [CommRing R] (S : Finset ι) :
    letI := (mixedMap R S).toRingHom.toAlgebra
    IsLocalization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R))
      (MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ)))) := by
  let f := (splitExponent S).toMultiplicative
  let := (MonoidAlgebra.mapDomainRingHom R f).toAlgebra
  have := mixed_localization R S
  let := (mixedMap R S).toRingHom.toAlgebra
  apply IsLocalization.of_ringEquiv_left (polyEquiv R).toRingEquiv
    (M₁ := Submonoid.powers
      (MonoidAlgebra.single (Multiplicative.ofAdd (denominator S)) (1 : R)))
  · rw [Submonoid.map_powers]
    change Submonoid.powers (polyEquiv R (∏ j ∈ S, MvPolynomial.X j)) = _
    rw [product_denominator]
  · intro a
    rfl

private def exponentEquiv (S : Finset ι) :
    Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ)) ≃*
      Multiplicative ({j // j ∉ S} →₀ ℕ) × Multiplicative (S →₀ ℤ) where
  toFun x := (.ofAdd (Finsupp.equivFunOnFinite.symm x.toAdd.2),
    .ofAdd (Finsupp.equivFunOnFinite.symm x.toAdd.1))
  invFun x := .ofAdd (x.2.toAdd, x.1.toAdd)
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd
        (Finsupp.equivFunOnFinite.symm_apply_apply x.1.toAdd)
    · exact congrArg Multiplicative.ofAdd
        (Finsupp.equivFunOnFinite.symm_apply_apply x.2.toAdd)
  map_mul' _ _ := by
    apply Prod.ext
    · apply congrArg Multiplicative.ofAdd
      ext j
      rfl
    · apply congrArg Multiplicative.ofAdd
      ext j
      rfl

private def mixedProductEquiv (R : Type u) [CommRing R] (S : Finset ι) :
    MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ))) ≃ₐ[R]
      MvPolynomial {j // j ∉ S} (MonoidAlgebra R (Multiplicative (S →₀ ℤ))) :=
  (MonoidAlgebra.domCongr R R (exponentEquiv S)).trans
    ((MonoidAlgebra.curryAlgEquiv R).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv R
        (MonoidAlgebra R (Multiplicative (S →₀ ℤ))) ({j // j ∉ S} →₀ ℕ)).symm)

/-- Inverting selected polynomial variables gives the product of their Laurent algebra
and the polynomial algebra in the remaining variables. -/
def coordinateLocalizationEquiv (R : Type u) [CommRing R] (S : Finset ι) :
    Localization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R)) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (S →₀ ℤ)) ⊗[R] MvPolynomial {j // j ∉ S} R := by
  let := (mixedMap R S).toRingHom.toAlgebra
  have := polynomial_localization R S
  have : IsScalarTower R (MvPolynomial ι R)
      (MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ)))) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((mixedMap R S).commutes r).symm)
  let e := (MvPolynomial.algebraTensorAlgEquiv (σ := {j // j ∉ S}) R
    (MonoidAlgebra R (Multiplicative (S →₀ ℤ)))).restrictScalars R
  exact ((IsLocalization.algEquiv
    (Submonoid.powers (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R)))
    (Localization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R)))
    (MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ))))).restrictScalars R).trans
      ((mixedProductEquiv R S).trans e.symm)

private theorem localization_apply (R : Type u) [CommRing R] (S : Finset ι)
    (p : MvPolynomial ι R) :
    coordinateLocalizationEquiv R S (algebraMap (MvPolynomial ι R)
      (Localization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R))) p) =
      (MvPolynomial.algebraTensorAlgEquiv (σ := {j // j ∉ S}) R
        (MonoidAlgebra R (Multiplicative (S →₀ ℤ)))).symm
          (mixedProductEquiv R S (mixedMap R S p)) := by
  let := (mixedMap R S).toRingHom.toAlgebra
  have := polynomial_localization R S
  have : IsScalarTower R (MvPolynomial ι R)
      (MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ)))) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((mixedMap R S).commutes r).symm)
  have h := (IsLocalization.algEquiv
    (Submonoid.powers (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R)))
    (Localization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R)))
    (MonoidAlgebra R (Multiplicative ((S → ℤ) × ({j // j ∉ S} → ℕ))))).commutes p
  exact congrArg (fun z =>
    (MvPolynomial.algebraTensorAlgEquiv (σ := {j // j ∉ S}) R
      (MonoidAlgebra R (Multiplicative (S →₀ ℤ)))).symm
        (mixedProductEquiv R S z)) h

omit [Finite ι] in
private theorem tag_symm_single {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] (m : M) (a : A) :
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv R A M).symm
        (MonoidAlgebra.single (Multiplicative.ofAdd m) a) = AddMonoidAlgebra.single m a := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R A M).injective
  rw [AlgEquiv.apply_symm_apply, AddMonoidAlgebra.toMultiplicativeAlgEquiv_single]

omit [Finite ι] in
private theorem mixed_monomial (R : Type u) [CommRing R] (S : Finset ι)
    (d : ι →₀ ℕ) (r : R) :
    mixedMap R S (MvPolynomial.monomial d r) =
      MonoidAlgebra.single (Multiplicative.ofAdd (splitExponent S d)) r := by
  change (MonoidAlgebra.mapDomainAlgHom R R (splitExponent S).toMultiplicative)
    ((AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (ι →₀ ℕ))
      (AddMonoidAlgebra.single d r)) = _
  rw [AddMonoidAlgebra.toMultiplicativeAlgEquiv_single]
  change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single _ _) = _
  exact MonoidAlgebra.mapDomain_single

private theorem mixedProduct_single (R : Type u) [CommRing R] (S : Finset ι)
    (y : (S → ℤ) × ({j // j ∉ S} → ℕ)) (r : R) :
    mixedProductEquiv R S (MonoidAlgebra.single (Multiplicative.ofAdd y) r) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm y.2)
        (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm y.1)) r) := by
  change (AddMonoidAlgebra.toMultiplicativeAlgEquiv R
    (MonoidAlgebra R (Multiplicative (S →₀ ℤ))) ({j // j ∉ S} →₀ ℕ)).symm
      ((MonoidAlgebra.curryAlgEquiv R)
        ((MonoidAlgebra.domCongr R R (exponentEquiv S))
          (MonoidAlgebra.single (Multiplicative.ofAdd y) r))) = _
  rw [MonoidAlgebra.domCongr_single]
  change (AddMonoidAlgebra.toMultiplicativeAlgEquiv R
    (MonoidAlgebra R (Multiplicative (S →₀ ℤ))) ({j // j ∉ S} →₀ ℕ)).symm
      ((MonoidAlgebra.curryAlgEquiv R) (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm y.2),
          Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm y.1)) r)) = _
  rw [MonoidAlgebra.curryAlgEquiv_single]
  exact tag_symm_single (R := R) _ _

private theorem coordinate_monomial (R : Type u) [CommRing R] (S : Finset ι)
    (d : ι →₀ ℕ) (r : R) :
    coordinateLocalizationEquiv R S (algebraMap (MvPolynomial ι R)
      (Localization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι R)))
        (MvPolynomial.monomial d r)) =
      MonoidAlgebra.single (Multiplicative.ofAdd
        (Finsupp.equivFunOnFinite.symm (splitExponent S d).1)) r ⊗ₜ[R]
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (splitExponent S d).2) 1 := by
  rw [localization_apply, mixed_monomial, mixedProduct_single,
    MvPolynomial.algebraTensorAlgEquiv_symm_monomial]

/-- A selected variable becomes its Laurent coordinate after localization. -/
theorem coordinateLocalization_X_mem (R : Type u) [CommRing R] (S : Finset ι) (j : S) :
    coordinateLocalizationEquiv R S (algebraMap (MvPolynomial ι R)
      (Localization.Away (∏ k ∈ S, (MvPolynomial.X k : MvPolynomial ι R)))
        (MvPolynomial.X j.val)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single j (1 : ℤ))) 1 ⊗ₜ[R] 1 := by
  classical
  have hz : Finsupp.equivFunOnFinite.symm (splitExponent S (Finsupp.single j.val 1)).1 =
      Finsupp.single j (1 : ℤ) := by
    ext k
    change ((Finsupp.single j.val (1 : ℕ)) k.val : ℤ) = (Finsupp.single j (1 : ℤ)) k
    by_cases h : j = k
    · subst k; simp
    · have hv : j.val ≠ k.val := fun e => h (Subtype.ext e)
      simp [h, hv]
  have hn : Finsupp.equivFunOnFinite.symm (splitExponent S (Finsupp.single j.val 1)).2 = 0 := by
    ext k
    change (Finsupp.single j.val (1 : ℕ)) k.val = 0
    have hv : j.val ≠ k.val := fun e => k.property (e ▸ j.property)
    simp [hv]
  change coordinateLocalizationEquiv R S (algebraMap _ _
    (MvPolynomial.monomial (Finsupp.single j.val 1) 1)) = _
  rw [coordinate_monomial, hz, hn]
  simp

/-- An unselected variable becomes its polynomial coordinate after localization. -/
theorem coordinateLocalization_X_not_mem (R : Type u) [CommRing R] (S : Finset ι)
    (j : {j // j ∉ S}) :
    coordinateLocalizationEquiv R S (algebraMap (MvPolynomial ι R)
      (Localization.Away (∏ k ∈ S, (MvPolynomial.X k : MvPolynomial ι R)))
        (MvPolynomial.X j.val)) = 1 ⊗ₜ[R] MvPolynomial.X j := by
  classical
  have hz : Finsupp.equivFunOnFinite.symm (splitExponent S (Finsupp.single j.val 1)).1 = 0 := by
    ext k
    change ((Finsupp.single j.val (1 : ℕ)) k.val : ℤ) = 0
    have hv : j.val ≠ k.val := fun e => j.property (e.symm ▸ k.property)
    simp [hv]
  have hn : Finsupp.equivFunOnFinite.symm (splitExponent S (Finsupp.single j.val 1)).2 =
      Finsupp.single j 1 := by
    ext k
    change (Finsupp.single j.val (1 : ℕ)) k.val = (Finsupp.single j (1 : ℕ)) k
    by_cases h : j = k
    · subst k; simp
    · have hv : j.val ≠ k.val := fun e => h (Subtype.ext e)
      simp [h, hv]
  change coordinateLocalizationEquiv R S (algebraMap _ _
    (MvPolynomial.monomial (Finsupp.single j.val 1) 1)) = _
  rw [coordinate_monomial, hz, hn]
  rfl

end GroupActions
