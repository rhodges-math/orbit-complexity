import OrbitComplexity.FrobeniusSplitting.Normality.Covers.OpenDenominatorData

/-! # Joint denominator and parameter models from chosen coefficient algebras -/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w z
namespace FrobeniusSplitting

/-- One coefficient enlargement retains finite open denominators and all prescribed parameters. -/
theorem exists_open_denominator_models {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (M : C ⥤ CommAlgCat.{u} S)
    [∀ i, Algebra.FinitePresentation S (M.obj i)] [∀ i, Algebra.Smooth S (M.obj i)]
    (F : C ⥤ CommAlgCat.{u} K) (e : ∀ i, K ⊗[S] M.obj i ≃ₐ[K] F.obj i)
    (he : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e i).toAlgHom)
    (hopen : ∀ i j (f : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)))
    (V : C → Type z) [∀ i, Finite (V i)] (values : ∀ i, V i → F.obj i) :
    openDenominatorSpec S M F e V values := by
  classical
  dsimp only [openDenominatorSpec]
  let arrows := Σ i : C, Σ j : C, i ⟶ j
  choose L hL a hcover hlocal using fun b : arrows ↦
    (isOpenImmersion_iff_away_maps (F.map b.2.2).hom.toRingHom).mp
      (hopen b.1 b.2.1 b.2.2)
  let (b : arrows) : Finite (L b) := hL b
  let W (i : C) := V i ⊕ (Σ j : C, Σ f : i ⟶ j, L ⟨i, j, f⟩)
  let value (i : C) : W i → F.obj i :=
    Sum.elim (values i) (fun b ↦ a ⟨i, b.1, b.2.1⟩ b.2.2)
  obtain ⟨T, hST, P, eP, hT, hP, hfp, hsm, heval, hmaps, hvalues⟩ :=
    exists_scalar_image_graph S hS (fun i ↦ (M.obj i : Type u))
      (fun i ↦ (F.obj i : Type u)) e Set.univ (fun _ _ ↦ inferInstance)
      (fun b : arrows ↦ b.1) (fun b : arrows ↦ b.2.1)
      (fun b ↦ (F.map b.2.2).hom) W value
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let d {i j : C} (f : i ⟶ j) : P i →ₐ[T] P j :=
    (((F.map f).hom.restrictScalars T).comp (P i).val).codRestrict (P j)
      (fun x ↦ hmaps ⟨i, j, f⟩ x.property)
  have hd (i j : C) (f : i ⟶ j) (x : P i) : (d f x).val = (F.map f).hom x.val := rfl
  have hv (i : C) (v : V i) : values i v ∈ P i := hvalues i (.inl v)
  have ha (b : arrows) (j : L b) : a b j ∈ P b.1 :=
    hvalues b.1 (.inr ⟨b.2.1, b.2.2, j⟩)
  let g (b : arrows) (j : L b) : P b.1 := ⟨a b j, ha b j⟩
  have hevalOne (i : C) (x : P i) : eP i ((1 : K) ⊗ₜ[T] x) = x.val := by
    simpa only [map_one, one_mul] using heval i 1 x
  have hu := scalarImage_diagram_iso M F (FaithfulSMul.algebraMap_injective T K)
    e he P hP d hd
  exact ⟨L, hL, a, hcover, hlocal, T, hST, P, eP, d, hd, hT, hfp,
    (fun i ↦ hsm i (Set.mem_univ i)), hevalOne, hv, hP,
    ⟨g, fun b j ↦ hevalOne b.1 (g b j)⟩, hu⟩

end FrobeniusSplitting
