import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.PrincipalImages
import OrbitComplexity.FrobeniusSplitting.Normality.DiagramCovers
import OrbitComplexity.FrobeniusSplitting.Normality.ImageGenerators
import OrbitComplexity.FrobeniusSplitting.Normality.SubalgebraSquares
import OrbitComplexity.FrobeniusSplitting.Normality.PushoutFactors
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Open arithmetic diagrams

Finite affine open diagrams descend with their pushout squares and selected smoothness.
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

open PrincipalDiagram

variable {C : Type v} [Category.{w} C] {K : Type u} [CommRing K]
    {S : Subalgebra ℤ K} (D₀ : C ⥤ CommAlgCat.{u} S) (D : C ⥤ CommAlgCat.{u} K)
    (L : DiagramArrow C → Type u)
    (g : ∀ b, L b → D₀.obj b.1) (a : ∀ b, L b → D.obj b.1)

set_option maxHeartbeats 400000 in
private theorem imageSquare_pushout {R : Subalgebra ℤ K}
    [Algebra S R] [IsScalarTower S R K]
    (models : ∀ n, Subalgebra R (genericAt D L a n))
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (preserve : ∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
      maps b (x : genericAt D L a (edgeSrc L b)) ∈ models (edgeTgt L b))
    (hbase : ∀ b, maps (.inl b) = (D.map b.2.2).hom)
    (comparison : ∀ i, K ⊗[R] models (.inl i) ≃ₐ[K] D.obj i)
    (heval : ∀ i (x : models (.inl i)), comparison i ((1 : K) ⊗ₜ[R] x) = x.val)
    (hopen : ∀ b : DiagramArrow C, AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl b)).toRingHom)))
    {i j k l : C} (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l)
    (hpush : CategoryTheory.IsPushout
      (CommRingCat.ofHom (D.map f).hom.toRingHom)
      (CommRingCat.ofHom (D.map g).hom.toRingHom)
      (CommRingCat.ofHom (D.map p).hom.toRingHom)
      (CommRingCat.ofHom (D.map q).hom.toRingHom))
    {T ι : Type*} [CommRing T] [Algebra S T]
    (eT : K ⊗[S] T ≃ₐ[K] D.obj l) (Pgen : Algebra.Generators S T ι)
    (hZ : (show Subalgebra R (D.obj l) from models (.inl l)) =
      (scalarImageHom (R := R) eT).range)
    (n : ι → ℕ) (x : ∀ v, Fin (n v) → D.obj j) (y : ∀ v, Fin (n v) → D.obj k)
    (hfactor : ∀ v, eT ((1 : K) ⊗ₜ[S] Pgen.val v) =
      ∑ z, (D.map p).hom (x v z) * (D.map q).hom (y v z))
    (hx : ∀ v z, x v z ∈ models (.inl j))
    (hy : ∀ v z, y v z ∈ models (.inl k)) :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl ⟨i, j, f⟩)).toRingHom)
      (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl ⟨i, k, g⟩)).toRingHom)
      (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl ⟨j, l, p⟩)).toRingHom)
      (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl ⟨k, l, q⟩)).toRingHom) := by
  let M : Subalgebra R (D.obj i) := models (.inl i)
  let N : Subalgebra R (D.obj j) := models (.inl j)
  let P : Subalgebra R (D.obj k) := models (.inl k)
  let Z : Subalgebra R (D.obj l) := models (.inl l)
  let f₀ : M →ₐ[R] N := imageMap D L a models maps preserve (.inl ⟨i, j, f⟩)
  let g₀ : M →ₐ[R] P := imageMap D L a models maps preserve (.inl ⟨i, k, g⟩)
  let p₀ : N →ₐ[R] Z := imageMap D L a models maps preserve (.inl ⟨j, l, p⟩)
  let q₀ : P →ₐ[R] Z := imageMap D L a models maps preserve (.inl ⟨k, l, q⟩)
  have hf₀ (z : M) : (f₀ z).val = (D.map f).hom z.val :=
    AlgHom.congr_fun (hbase ⟨i, j, f⟩) z.val
  have hg₀ (z : M) : (g₀ z).val = (D.map g).hom z.val :=
    AlgHom.congr_fun (hbase ⟨i, k, g⟩) z.val
  have hp₀ (z : N) : (p₀ z).val = (D.map p).hom z.val :=
    AlgHom.congr_fun (hbase ⟨j, l, p⟩) z.val
  have hq₀ (z : P) : (q₀ z).val = (D.map q).hom z.val :=
    AlgHom.congr_fun (hbase ⟨k, l, q⟩) z.val
  have hflatf : f₀.toRingHom.Flat := by
    have : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f₀.toRingHom)) := hopen ⟨i, j, f⟩
    exact (AlgebraicGeometry.Flat.SpecMap_iff
      (f := CommRingCat.ofHom f₀.toRingHom)).mp inferInstance
  have hflatg : g₀.toRingHom.Flat := by
    have : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom g₀.toRingHom)) := hopen ⟨i, k, g⟩
    exact (AlgebraicGeometry.Flat.SpecMap_iff
      (f := CommRingCat.ofHom g₀.toRingHom)).mp inferInstance
  have hgen : p₀.range ⊔ q₀.range = ⊤ := by
    apply model_images_eq_top Pgen eT Z hZ p₀ q₀
    intro v
    refine ⟨n v, (fun z ↦ ⟨x v z, hx v z⟩), (fun z ↦ ⟨y v z, hy v z⟩), ?_⟩
    apply (hfactor v).trans
    apply Finset.sum_congr rfl
    intro z _
    exact congrArg₂ (· * ·) (hp₀ ⟨x v z, hx v z⟩).symm
      (hq₀ ⟨y v z, hy v z⟩).symm
  exact isPushout_of_subalgebra_models R (D.map f).hom (D.map g).hom
    (D.map p).hom (D.map q).hom hpush M N P Z f₀ g₀ p₀ q₀ hf₀ hg₀ hp₀ hq₀
    (comparison i) (comparison j) (comparison k) (heval i) (heval j) (heval k)
    hflatf hflatg hgen

/-- Finite affine open diagrams admit arithmetic models preserving their pushout squares. -/
theorem exists_open_arithmetic_diagram [Finite C] [∀ i j : C, Finite (i ⟶ j)]
    [∀ i, Algebra.FinitePresentation K (D.obj i)]
    (hopen : ∀ i j (f : i ⟶ j), AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom)))
    (smoothNodes : Set C) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K (D.obj i)) :
    ∃ (R : Subalgebra ℤ K) (D₁ : C ⥤ CommAlgCat.{u} R)
      (e₁ : ∀ i, K ⊗[R] D₁.obj i ≃ₐ[K] D.obj i),
      R.FG ∧ (∀ i, Algebra.FinitePresentation R (D₁.obj i)) ∧
      (∀ i, i ∈ smoothNodes → Algebra.Smooth R (D₁.obj i)) ∧
      (∀ i j (f : i ⟶ j), (e₁ j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (D₁.map f).hom) =
        (D.map f).hom.comp (e₁ i).toAlgHom) ∧
      (∀ i j (f : i ⟶ j), AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (D₁.map f).hom.toRingHom))) ∧
      ∀ (i j k l : C) (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l),
        CategoryTheory.IsPushout (CommRingCat.ofHom (D.map f).hom.toRingHom)
          (CommRingCat.ofHom (D.map g).hom.toRingHom)
          (CommRingCat.ofHom (D.map p).hom.toRingHom)
          (CommRingCat.ofHom (D.map q).hom.toRingHom) →
        CategoryTheory.IsPushout (CommRingCat.ofHom (D₁.map f).hom.toRingHom)
          (CommRingCat.ofHom (D₁.map g).hom.toRingHom)
          (CommRingCat.ofHom (D₁.map p).hom.toRingHom)
          (CommRingCat.ofHom (D₁.map q).hom.toRingHom) := by
  classical
  obtain ⟨L, finiteL, a, S, D₀, e, hfg, hfp, hsmooth, hnatural,
    hcover, hlocal, g, hg⟩ := exists_open_diagram_elements D hopen smoothNodes hsm
  let (b : DiagramArrow C) : Finite (L b) := finiteL b
  let (i : C) : Algebra.FinitePresentation S (D₀.obj i) := hfp i
  let V (i : C) := Fin (Algebra.Presentation.ofFinitePresentationVars S (D₀.obj i))
  let W (i : C) := Fin (Algebra.Presentation.ofFinitePresentationRels S (D₀.obj i))
  let presentations (i : C) : Algebra.Presentation S (D₀.obj i) (V i) (W i) :=
    Algebra.Presentation.ofFinitePresentation S (D₀.obj i)
  let values (i : C) (z : V i) : D.obj i :=
    e i ((1 : K) ⊗ₜ[S] (presentations i).val z)
  obtain ⟨J, finiteJ, extra, factors⟩ := exists_finite_pushout_factors D V values
  let (i : C) : Finite (J i) := finiteJ i
  let I : PrincipalNode L → Type (max v w)
    | .inl i => J i
    | .inr _ => PEmpty
  let (n : PrincipalNode L) : Finite (I n) := by
    rcases n with i | p
    · change Finite (J i)
      infer_instance
    · change Finite PEmpty
      infer_instance
  let elements : ∀ n, I n → genericAt D L a n
    | .inl i => extra i
    | .inr _ => fun z ↦ nomatch z
  let maps := genericMaps D L a hlocal
  obtain ⟨R, hSR, hmodels⟩ := exists_open_images D₀ D L g a hfg e hnatural hg
    hlocal hcover maps (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun b j ↦ by
      apply AlgHom.ext
      intro x
      exact (AlgEquiv.ofBijective
        (Localization.awayMapₐ (D.map b.2.2).hom (a b j)) (hlocal b j)).apply_symm_apply x)
    smoothNodes hsmooth I elements
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  obtain ⟨models, comparison, preserve, hfgR, hintrinsic, hfpR, hsmoothR,
    heval, hopenR, helts⟩ := hmodels
  have hevalOne (i : C) (z : models (.inl i)) :
      comparison (.inl i) ((1 : K) ⊗ₜ[R] z) = z.val := by
    rw [heval, map_one, one_mul]
  let fm {i j : C} (f : i ⟶ j) : models (.inl i) →ₐ[R] models (.inl j) :=
    imageMap D L a models maps preserve (.inl ⟨i, j, f⟩)
  let D₁ : C ⥤ CommAlgCat.{u} R :=
    { obj := fun i ↦ CommAlgCat.of R (models (.inl i))
      map := fun f ↦ CommAlgCat.ofHom (fm f)
      map_id := by
        intro i
        ext x
        change (D.map (𝟙 i)).hom x.val = x.val
        exact AlgHom.congr_fun
          (congrArg (fun t : D.obj i ⟶ D.obj i ↦ t.hom) (D.map_id i)) x.val
      map_comp := by
        intro i j k f h
        ext x
        change (D.map (f ≫ h)).hom x.val = (D.map h).hom ((D.map f).hom x.val)
        exact AlgHom.congr_fun
          (congrArg (fun t : D.obj i ⟶ D.obj k ↦ t.hom) (D.map_comp f h)) x.val }
  refine ⟨R, D₁, (fun i ↦ comparison (.inl i)), hfgR,
    (fun i ↦ hfpR (.inl i)), hsmoothR, ?_, ?_, ?_⟩
  · intro i j f
    ext x
    change comparison (.inl j) ((1 : K) ⊗ₜ[R] fm f x) =
      (D.map f).hom (comparison (.inl i) ((1 : K) ⊗ₜ[R] x))
    rw [heval, heval]
    simp only [map_one, one_mul]
    rfl
  · intro i j f
    exact hopenR ⟨i, j, f⟩
  · intro i j k l f g p q hpush
    obtain ⟨n, x, y, hfactor, hx, hy⟩ := factors i j k l f g p q hpush
    have hxmem (z : V l) (a : Fin (n z)) : x z a ∈ models (.inl j) := by
      obtain ⟨b, hb⟩ := hx z a
      exact hb ▸ helts (.inl j) b
    have hymem (z : V l) (a : Fin (n z)) : y z a ∈ models (.inl k) := by
      obtain ⟨b, hb⟩ := hy z a
      exact hb ▸ helts (.inl k) b
    have hZ : (show Subalgebra R (D.obj l) from models (.inl l)) =
        (scalarImageHom (R := R) (e l)).range := hintrinsic (.inl l)
    exact imageSquare_pushout D L a models maps preserve (fun _ ↦ rfl)
      (fun i ↦ comparison (.inl i)) hevalOne hopenR f g p q hpush
      (e l) (presentations l).toGenerators hZ n x y hfactor hxmem hymem

end FrobeniusSplitting
