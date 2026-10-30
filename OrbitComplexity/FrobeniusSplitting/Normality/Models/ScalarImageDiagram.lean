import OrbitComplexity.FrobeniusSplitting.Normality.Models.ScalarImageBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.EmbeddedDiagrams

/-! # Scalar-image diagrams and their coefficient base changes -/

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- Flat intrinsic image diagrams identify naturally with their chosen coefficient base change. -/
theorem scalarImage_diagram_iso {C : Type v} [Category.{w} C]
    {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    (M : C ⥤ CommAlgCat.{u} S) (F : C ⥤ CommAlgCat.{u} K)
    [∀ i, Algebra R (F.obj i)] [∀ i, IsScalarTower R K (F.obj i)]
    [∀ i, Module.Flat S (M.obj i)]
    (hi : Function.Injective (algebraMap R K))
    (e : ∀ i, K ⊗[S] M.obj i ≃ₐ[K] F.obj i)
    (he : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e i).toAlgHom)
    (P : ∀ i, Subalgebra R (F.obj i))
    (hP : ∀ i, P i = (scalarImageHom (R := R) (e i)).range)
    (d : ∀ {i j}, (i ⟶ j) → P i →ₐ[R] P j)
    (hd : ∀ i j (f : i ⟶ j) z, (d f z).val = (F.map f).hom z.val) :
    let N := modelFunctor (fun i ↦ P i) (F ⋙ forget₂ (CommAlgCat K) CommRingCat)
      d (fun i ↦ (P i).val.toRingHom) (fun _ ↦ Subtype.val_injective) hd
    ∃ u : fixedFibreDiagram (R := R) (M := R) M ≅ N,
      ∀ i z, (P i).val ((u.hom.app i).hom z) = scalarImageHom (R := R) (e i) z := by
  let N := modelFunctor (fun i ↦ P i) (F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    d (fun i ↦ (P i).val.toRingHom) (fun _ ↦ Subtype.val_injective) hd
  have hu (i : C) := scalarImage_baseChange (R := R) (e i) hi
  choose u hu using hu
  let q (i : C) : R ⊗[S] M.obj i ≃ₐ[R] P i :=
    (u i).trans (Subalgebra.equivOfEq _ _ (hP i).symm)
  have hq (i : C) (z : R ⊗[S] M.obj i) :
      ((q i z : P i) : F.obj i) = scalarImageHom (R := R) (e i) z := hu i z
  have hn (i j : C) (f : i ⟶ j) (z : R ⊗[S] M.obj i) :
      scalarImageHom (R := R) (e j)
          (Algebra.TensorProduct.lTensor (S := R) R (M.map f).hom z) =
        (F.map f).hom (scalarImageHom (R := R) (e i) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul r m =>
      exact AlgHom.congr_fun (he i j f) (algebraMap R K r ⊗ₜ[S] m)
    | add z t hz ht => simp only [map_add, hz, ht]
  let u₀ : fixedFibreDiagram (R := R) (M := R) M ≅ N :=
    NatIso.ofComponents (fun i ↦ CommAlgCat.isoMk (q i)) (by
      intro i j f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      apply Subtype.ext
      change ((q j (Algebra.TensorProduct.lTensor (S := R) R (M.map f).hom z) : P j) :
        F.obj j) = (d f (q i z)).val
      rw [hq, hd, hq]
      exact hn i j f z)
  exact ⟨u₀, hq⟩

end FrobeniusSplitting
