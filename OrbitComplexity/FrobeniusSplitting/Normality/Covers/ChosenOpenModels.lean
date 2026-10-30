import OrbitComplexity.FrobeniusSplitting.Normality.Covers.ChosenOpenModelsData

/-! # Open coordinate models with their chosen scalar comparisons -/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- Finite principal witnesses give open models retaining the entire chosen base change. -/
theorem exists_chosen_open_models {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (M : C ⥤ CommAlgCat.{u} S)
    [∀ i, Algebra.FinitePresentation S (M.obj i)] [∀ i, Algebra.Smooth S (M.obj i)]
    (F : C ⥤ CommAlgCat.{u} K) (e : ∀ i, K ⊗[S] M.obj i ≃ₐ[K] F.obj i)
    (he : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e i).toAlgHom)
    (L : (Σ i : C, Σ j : C, i ⟶ j) → Type u) [∀ b, Finite (L b)]
    (a : ∀ b, L b → F.obj b.1) (g : ∀ b, L b → M.obj b.1)
    (hcover : ∀ b, Ideal.span (Set.range (fun j ↦ (F.map b.2.2).hom (a b j))) = ⊤)
    (hlocal : ∀ b j, Function.Bijective
      (Localization.awayMap (F.map b.2.2).hom.toRingHom (a b j)))
    (hg : ∀ b j, e b.1 ((1 : K) ⊗ₜ[S] g b j) = a b j) :
    chosenOpenModelSpec S M F e := by
  classical
  obtain ⟨R, hSR, N, eN, _, hR, hfp, hsm, hn, hi, _, hopen, hpush, hintrinsic⟩ :=
    exists_open_model_maps M F L g a hS e he hcover hlocal hg Set.univ
      (fun _ _ ↦ inferInstance) (fun x : Empty ↦ nomatch x)
      (fun x : Empty ↦ nomatch x) (fun x : Empty ↦ nomatch x)
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  choose v hv using hintrinsic
  have hb (i : C) := scalarImage_baseChange (R := R) (e i)
    (FaithfulSMul.algebraMap_injective R K)
  choose b hb using hb
  let q (i : C) : R ⊗[S] M.obj i ≃ₐ[R] N.obj i := (b i).trans (v i).symm
  have hq (i : C) (z : R ⊗[S] M.obj i) :
      eN i ((1 : K) ⊗ₜ[R] q i z) = scalarImageHom (R := R) (e i) z := by
    rw [hv]
    change ((v i) ((v i).symm (b i z))).val = _
    rw [AlgEquiv.apply_symm_apply]
    exact hb i z
  have hemap (i j : C) (f : i ⟶ j) (z : R ⊗[S] M.obj i) :
      scalarImageHom (R := R) (e j)
          (Algebra.TensorProduct.lTensor (S := R) R (M.map f).hom z) =
        (F.map f).hom (scalarImageHom (R := R) (e i) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul r m => exact AlgHom.congr_fun (he i j f) (algebraMap R K r ⊗ₜ[S] m)
    | add z t hz ht => simp only [map_add, hz, ht]
  let u : fixedFibreDiagram (R := R) (M := R) M ≅ N :=
    NatIso.ofComponents (fun i ↦ CommAlgCat.isoMk (q i)) (by
      intro i j f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      apply hi j
      change eN j ((1 : K) ⊗ₜ[R]
          q j (Algebra.TensorProduct.lTensor (S := R) R (M.map f).hom z)) =
        eN j ((1 : K) ⊗ₜ[R] (N.map f).hom (q i z))
      rw [hq]
      have h := AlgHom.congr_fun (hn i j f) ((1 : K) ⊗ₜ[R] q i z)
      change eN j ((1 : K) ⊗ₜ[R] (N.map f).hom (q i z)) =
        (F.map f).hom (eN i ((1 : K) ⊗ₜ[R] q i z)) at h
      rw [h, hq]
      exact hemap i j f z)
  exact ⟨R, hSR, N, eN, hR, hfp, (fun i ↦ hsm i (Set.mem_univ i)),
    hn, hi, hopen, hpush, u, hq⟩

end FrobeniusSplitting
