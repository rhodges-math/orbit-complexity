import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedSourceModels
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams

/-! # Simultaneous coefficient extensions and product squares

These algebraic helpers retain a finite family over one coefficient ring and
express the maps inherited from its specified arrows.
-/

open CategoryTheory
open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u v w

/-- A specified finite family of flat models becomes smooth after one common
coefficient extension, with every node retained as its tensor product. -/
theorem exists_smooth_family_extension {I : Type v} [Finite I]
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (M A : I → Type u) [∀ i, CommRing (M i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FinitePresentation S (M i)] [∀ i, Module.Flat S (M i)]
    [∀ i, Algebra.Smooth K (A i)] (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ ∀ i, Algebra.Smooth R (R ⊗[S] M i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose R hSR hfg hsm using fun i => exists_smooth_model_extension S hS (M i) (e i)
  have hsfg (s : Finset I) : (s.sup R).FG := by
    induction s using Finset.induction_on with
    | empty => simpa using (Subalgebra.fg_adjoin_finset (R := ℤ) (∅ : Finset K))
    | insert i s hi ih => rw [Finset.sup_insert]; exact (hfg i).sup ih
  let U : Subalgebra ℤ K := S ⊔ Finset.univ.sup R
  have hSU : S ≤ U := le_sup_left
  let : Algebra S U := (Subalgebra.inclusion hSU).toAlgebra
  have : IsScalarTower S U K := Subalgebra.inclusion.isScalarTower_right hSU K
  refine ⟨U, hSU, hS.sup (hsfg Finset.univ), ?_⟩
  intro i
  have hRU : R i ≤ U := (Finset.le_sup (Finset.mem_univ i)).trans le_sup_right
  let : Algebra S (R i) := (Subalgebra.inclusion (hSR i)).toAlgebra
  let : Algebra (R i) U := (Subalgebra.inclusion hRU).toAlgebra
  have : IsScalarTower S (R i) U := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Smooth (R i) (R i ⊗[S] M i) := hsm i
  let E : U ⊗[R i] (R i ⊗[S] M i) ≃ₐ[U] U ⊗[S] M i :=
    Algebra.TensorProduct.cancelBaseChange S (R i) U U (M i)
  exact Algebra.Smooth.of_equiv (R := U) (A := U ⊗[R i] (R i ⊗[S] M i)) E

/-- The product comparison preserves the first-factor projection. -/
theorem productModelEquiv_projection {R K A B C D : Type*}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R K] [Algebra R A] [Algebra R B] [Algebra K C] [Algebra K D]
    (eA : K ⊗[R] A ≃ₐ[K] C) (eB : K ⊗[R] B ≃ₐ[K] D) :
    (productModelEquiv eA eB).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K K)
          ((Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[R] B).restrictScalars R)) =
      (Algebra.TensorProduct.includeLeft : C →ₐ[K] C ⊗[K] D).comp eA.toAlgHom := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul k a =>
      change productModelEquiv eA eB (k ⊗ₜ[R] (a ⊗ₜ[R] (1 : B))) =
        eA (k ⊗ₜ[R] a) ⊗ₜ[K] (1 : D)
      rw [productModelEquiv_tmul]
      simp only [← Algebra.TensorProduct.one_def, map_one]

/-- Product retractions commute with every specified first-factor algebra map. -/
theorem pointedProductRetraction_natural {R A A' B : Type*}
    [CommRing R] [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B] (f : A →ₐ[R] A') (eps : B →ₐ[R] R) :
    (pointedProductRetraction (A := A') eps).comp
        (Algebra.TensorProduct.map f (AlgHom.id R B)) =
      f.comp (pointedProductRetraction (A := A) eps) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  change f a * algebraMap R A' (eps b) = f (a * algebraMap R A (eps b))
  rw [map_mul, f.commutes]

/-- Canonical generic comparisons of coefficient extensions preserve
all arrows of the original specified diagram. -/
theorem extendedComparison_natural {J : Type v} [Category.{w} J]
    {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    (P : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ i, K ⊗[S] P.obj i ≃ₐ[K] F.obj i)
    (he : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
        (F.map f).hom.comp (e i).toAlgHom) :
    let N := fixedFibreDiagram (R := R) (M := R) P
    let eR (i : J) : K ⊗[R] N.obj i ≃ₐ[K] F.obj i :=
      (Algebra.TensorProduct.cancelBaseChange S R K K (P.obj i)).trans (e i)
    ∀ i j (f : i ⟶ j), (eR j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (eR i).toAlgHom := by
  intro N eR i j f
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht
  | tmul k z =>
      induction z using TensorProduct.inductionOn with
      | add z t hz ht =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz ht
      | tmul r m =>
          change e j ((r • k) ⊗ₜ[S] (P.map f).hom m) =
            (F.map f).hom (e i ((r • k) ⊗ₜ[S] m))
          exact AlgHom.congr_fun (he i j f) ((r • k) ⊗ₜ[S] m)

/-- One pointed factor and one coefficient extension work for a specified
finite family of flat models of smooth algebras. -/
theorem exists_pointed_smooth_family {I : Type v} [Finite I]
    {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
    (S : Subalgebra ℤ K) (hS : S.FG) (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FinitePresentation S (M i)] [∀ i, Module.Flat S (M i)]
    [Algebra.Smooth K B] [∀ i, Algebra.Smooth K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) (eps : B →ₐ[K] K) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (H0 : Type u) (_ : CommRing H0) (_ : Algebra R H0)
        (eH : K ⊗[R] H0 ≃ₐ[K] B) (eps0 : H0 →ₐ[R] R),
        R.FG ∧ Algebra.Smooth R H0 ∧
        (∀ i, Algebra.Smooth R (R ⊗[S] M i)) ∧
        (∀ i, Algebra.Smooth R ((R ⊗[S] M i) ⊗[R] H0)) ∧
        ∀ (k : K) (h : H0),
          eps (eH (k ⊗ₜ[R] h)) = k * algebraMap R K (eps0 h) := by
  obtain ⟨R1, hSR1, hR1, hC1⟩ := exists_smooth_family_extension S hS M A e
  let : Algebra S R1 := (Subalgebra.inclusion hSR1).toAlgebra
  have : IsScalarTower S R1 K := Subalgebra.inclusion.isScalarTower_right hSR1 K
  obtain ⟨T, Q, ringQ, algQ, hT, hQ, eQ⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ K B
  let : CommRing Q := ringQ
  let : Algebra T Q := algQ
  have : Algebra.Smooth T Q := hQ
  let U : Subalgebra ℤ K := R1 ⊔ T
  have hR1U : R1 ≤ U := le_sup_left
  have hTU : T ≤ U := le_sup_right
  let : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  have : IsScalarTower T U K := Subalgebra.inclusion.isScalarTower_right hTU K
  let H := U ⊗[T] Q
  let eH1 : K ⊗[U] H ≃ₐ[K] B :=
    (Algebra.TensorProduct.cancelBaseChange T U K K Q).trans eQ.some.symm
  obtain ⟨R, hUR, H0, ringH0, algH0, eH, eps0, hR, hH0, hpoint⟩ :=
    exists_pointed_model_extension U (hR1.sup hT) H eH1 eps
  let : Algebra U R := (Subalgebra.inclusion hUR).toAlgebra
  have hR1R : R1 ≤ R := hR1U.trans hUR
  have hSR : S ≤ R := hSR1.trans hR1R
  let : Algebra R1 R := (Subalgebra.inclusion hR1R).toAlgebra
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R1 R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : CommRing H0 := ringH0
  let : Algebra R H0 := algH0
  have : Algebra.Smooth R H0 := hH0
  have hNode (i : I) : Algebra.Smooth R (R ⊗[S] M i) := by
    have : Algebra.Smooth R1 (R1 ⊗[S] M i) := hC1 i
    let E : R ⊗[R1] (R1 ⊗[S] M i) ≃ₐ[R] R ⊗[S] M i :=
      Algebra.TensorProduct.cancelBaseChange S R1 R R (M i)
    exact Algebra.Smooth.of_equiv (R := R) (A := R ⊗[R1] (R1 ⊗[S] M i)) E
  have hProd (i : I) : Algebra.Smooth R ((R ⊗[S] M i) ⊗[R] H0) :=
    Algebra.Smooth.comp R (R ⊗[S] M i) _
  exact ⟨R, hSR, H0, ringH0, algH0, eH, eps0, hR, hH0, hNode, hProd, hpoint⟩

end
end FrobeniusSplitting
