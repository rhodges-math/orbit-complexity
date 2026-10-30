import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorPatches
import Mathlib.RingTheory.Adjoin.FG

/-! # Principal coordinates over a common enlargement of the prior coefficient ring -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w t
namespace FrobeniusSplitting

private theorem finite_coordinate_lifts {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {J : Type v}
    (M : J → Type w) (C : J → Type t)
    [∀ j, CommRing (M j)] [∀ j, CommRing (C j)]
    [∀ j, Algebra S (M j)] [∀ j, Algebra K (C j)]
    (e : ∀ j, K ⊗[S] M j ≃ₐ[K] C j)
    {L : Type v} [Finite L] (node : L → J) (x : ∀ l, C (node l)) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let j : R →ₐ[S] K :=
        { toRingHom := R.val.toRingHom, commutes' := fun _ ↦ rfl }
      R.FG ∧ ∃ g : ∀ l, R ⊗[S] M (node l), ∀ l,
        e (node l) (Algebra.TensorProduct.map j (AlgHom.id S (M (node l))) (g l)) = x l := by
  classical
  choose n k y hsum using fun l ↦ TensorProduct.exists_sum_tmul_eq ((e (node l)).symm (x l))
  let coeffs : Set K := ⋃ l, Set.range (k l)
  have hcoeffs : coeffs.Finite := Set.finite_iUnion fun l ↦ Set.finite_range (k l)
  let R := S ⊔ Algebra.adjoin ℤ coeffs
  have hSR : S ≤ R := le_sup_left
  have hcore : Algebra.adjoin ℤ coeffs ≤ R := le_sup_right
  have hR : R.FG := hS.sup (Subalgebra.fg_def.mpr ⟨coeffs, hcoeffs, rfl⟩)
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let j : R →ₐ[S] K :=
    { toRingHom := R.val.toRingHom, commutes' := fun _ ↦ rfl }
  let k₀ (l : L) (m : Fin (n l)) : R :=
    ⟨k l m, hcore (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨l, m, rfl⟩))⟩
  refine ⟨R, hSR, hR, (fun l ↦ ∑ m, k₀ l m ⊗ₜ[S] y l m), fun l ↦ ?_⟩
  calc
    e (node l) (Algebra.TensorProduct.map j (AlgHom.id S (M (node l)))
        (∑ m, k₀ l m ⊗ₜ[S] y l m)) =
        e (node l) (∑ m, k l m ⊗ₜ[S] y l m) := by
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    _ = x l := by rw [← hsum l, AlgEquiv.apply_symm_apply]

/-- Principal refinements of the prior-model charts descend over one common
coefficient enlargement, retaining both chart labels and every factorization. -/
theorem exists_prior_patch_models {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {Y YK : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ i, IsAffine (U.X i))
    (V : YK.OpenCover.{u}) :
    let Q : YK.OpenCover.{u} := U.pullback₂ qY
    let (i : U.I₀) : Algebra S Γ(U.X i, ⊤) :=
      ((U.f i ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let (i : U.I₀) : Algebra K Γ(Q.X i, ⊤) :=
      ((Q.f i ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    let b : ∀ i, Q.X i ⟶ U.X i := fun i ↦ pullback.fst (U.f i) qY
    ∃ (e : ∀ i, K ⊗[S] Γ(U.X i, ⊤) ≃ₐ[K] Γ(Q.X i, ⊤)),
      (∀ i k x, e i (k ⊗ₜ[S] x) =
        algebraMap K Γ(Q.X i, ⊤) k * (b i).appTop.hom x) ∧
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let j : R →ₐ[S] K :=
        { toRingHom := R.val.toRingHom, commutes' := fun _ ↦ rfl }
      R.FG ∧ ∃ (L : Type u) (_ : Finite L) (prior : L → U.I₀) (endpoint : L → V.I₀)
        (s : ∀ l, Γ(Q.X (prior l), ⊤))
        (g : ∀ l, R ⊗[S] Γ(U.X (prior l), ⊤))
        (a : ∀ l, ((Q.X (prior l)).basicOpen (s l)).toScheme ⟶ V.X (endpoint l)),
        (∀ l, e (prior l) (Algebra.TensorProduct.map j
          (AlgHom.id S Γ(U.X (prior l), ⊤)) (g l)) = s l) ∧
        (∀ l, ((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l) = a l ≫ V.f (endpoint l)) ∧
        ∀ y : YK, ∃ l, ∃ z : ((Q.X (prior l)).basicOpen (s l)).toScheme,
          (((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l)) z = y := by
  classical
  let Q : YK.OpenCover.{u} := U.pullback₂ qY
  let (i : U.I₀) : Algebra S Γ(U.X i, ⊤) :=
    ((U.f i ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let (i : U.I₀) : Algebra K Γ(Q.X i, ⊤) :=
    ((Q.f i ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let (i : U.I₀) : IsAffine (U.X i) := hU i
  let b : ∀ i, Q.X i ⟶ U.X i := fun i ↦ pullback.fst (U.f i) qY
  have coords (i : U.I₀) : ∃ e : K ⊗[S] Γ(U.X i, ⊤) ≃ₐ[K] Γ(Q.X i, ⊤),
      (∀ k, e (k ⊗ₜ[S] (1 : Γ(U.X i, ⊤))) = algebraMap K Γ(Q.X i, ⊤) k) ∧
      (∀ x, e ((1 : K) ⊗ₜ[S] x) = (b i).appTop.hom x) ∧
      ∀ k x, e (k ⊗ₜ[S] x) = algebraMap K Γ(Q.X i, ⊤) k * (b i).appTop.hom x :=
    exists_prior_patch_coordinates base baseK qY h (U.f i)
  choose e hleft hright he using coords
  obtain ⟨L, hL, prior, endpoint, s, a, hfactor, hcover⟩ :=
    FrobeniusSplitting.exists_prior_patches base baseK qY h U hU V
  let : Finite L := hL
  obtain ⟨R, hSR, hR, g, hg⟩ := finite_coordinate_lifts S hS
    (fun i ↦ Γ(U.X i, ⊤)) (fun i ↦ Γ(Q.X i, ⊤)) e prior s
  exact ⟨e, he, R, hSR, hR, L, hL, prior, endpoint, s, g, a, hg, hfactor, hcover⟩

end FrobeniusSplitting
