import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Retention of finitely many zero relations -/

noncomputable section
namespace FrobeniusSplitting
open scoped TensorProduct
universe u v w

private theorem torsion_of_tmul_zero
    {S : Type u} [CommRing S] [IsDomain S]
    {K : Type v} [Field K] [Algebra S K] [FaithfulSMul S K]
    {M : Type w} [AddCommGroup M] [Module S M]
    (m : M) (hm : (1 : K) ⊗ₜ[S] m = 0) :
    ∃ s : S, s ≠ 0 ∧ s • m = 0 := by
  let F := FractionRing S
  let φ : F →ₐ[S] K := IsFractionRing.liftAlgHom
    (g := Algebra.ofId S K) (FaithfulSMul.algebraMap_injective S K)
  let : Algebra F K := φ.toAlgebra
  have : IsScalarTower S F K := IsScalarTower.of_algebraMap_eq
    (fun s => (φ.commutes s).symm)
  have hbase : (1 : K) ⊗ₜ[F] ((1 : F) ⊗ₜ[S] m) = 0 := by
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange S F K K M).injective
    simpa only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      one_smul, map_zero] using hm
  have hfrac : (1 : F) ⊗ₜ[S] m = 0 :=
    (Module.FaithfullyFlat.one_tmul_eq_zero_iff F (F ⊗[S] M) _).mp hbase
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S)
      (TensorProduct.mk S F M 1)).mp hfrac
  exact ⟨s.val, mem_nonZeroDivisors_iff_ne_zero.mp s.property, hs⟩

/-- Finitely many relations which vanish over a field vanish after adjoining finitely
many inverse coefficients to the prescribed coefficient ring. -/
theorem exists_retained_zero_relations
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Finite I] (M : I → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (x : ∀ i, M i) (hx : ∀ i, (1 : K) ⊗ₜ[S] x i = 0) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ ∀ i, (1 : R) ⊗ₜ[S] x i = 0 := by
  classical
  choose s hs hz using fun i => torsion_of_tmul_zero (x i) (hx i)
  let T : Set K := Set.range fun i => (algebraMap S K (s i))⁻¹
  let R : Subalgebra ℤ K := S ⊔ Algebra.adjoin ℤ T
  have hSR : S ≤ R := le_sup_left
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  refine ⟨R, hSR, hS.sup (Subalgebra.fg_def.mpr ⟨T, Set.finite_range _, rfl⟩), ?_⟩
  intro i
  let z : R := ⟨(algebraMap S K (s i))⁻¹,
    (le_sup_right : Algebra.adjoin ℤ T ≤ R) (Algebra.subset_adjoin ⟨i, rfl⟩)⟩
  have hne : algebraMap S K (s i) ≠ 0 := by
    intro h
    exact hs i ((FaithfulSMul.algebraMap_injective S K) (h.trans (map_zero _).symm))
  have hinv : z * algebraMap S R (s i) = 1 := by
    apply Subtype.ext
    exact inv_mul_cancel₀ hne
  calc
    (1 : R) ⊗ₜ[S] x i = (z * algebraMap S R (s i)) ⊗ₜ[S] x i := by rw [hinv]
    _ = z ⊗ₜ[S] ((s i) • x i) := by
      rw [TensorProduct.tmul_smul]
      congr 1
      exact ((Algebra.smul_def (s i) z).trans (mul_comm _ _)).symm
    _ = 0 := by rw [hz i, TensorProduct.tmul_zero]


end FrobeniusSplitting
