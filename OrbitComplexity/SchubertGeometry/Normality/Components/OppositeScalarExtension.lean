import OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

/-! # Scalar extension of finite coordinate diagrams -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private tensor_functor tensor_comparison tensor_comparison_natural
  tensor_map_hom tensor_open tensor_pushout from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private retain_refinements from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

/-- A diagram of algebras, its generic fibre and a scalar extension. -/
structure CoordinateExtensionData (K : Type u) [CommRing K] where
  /-- The labels of the closed coordinate diagrams. -/
  I : Type u
  /-- The category of affine charts. -/
  C : Type u
  /-- The category structure on the charts. -/
  [categoryC : Category.{u} C]
  /-- The coefficient subalgebra. -/
  S : Subalgebra ℤ K
  /-- The larger coefficient subalgebra. -/
  R : Subalgebra ℤ K
  /-- The coefficient extension. -/
  [algebraSR : Algebra S R]
  /-- The compatibility of the coefficient maps into the field. -/
  [towerSRK : IsScalarTower S R K]
  /-- The refinement functor on affine charts. -/
  H : C ⥤ C
  /-- The ambient coordinate diagram over the field. -/
  F : C ⥤ CommAlgCat.{u} K
  /-- The closed coordinate diagrams over the field. -/
  B : I → C ⥤ CommAlgCat.{u} K
  /-- The component maps into the closed coordinate diagrams. -/
  d : ∀ x : Σ _ : I, C, (H ⋙ F).obj x.2 ⟶ (B x.1).obj x.2
  /-- The joint coordinate diagram over the coefficient subalgebra. -/
  N : ((Σ _ : I, C) ⊕ C) ⥤ CommAlgCat.{u} S
  /-- The identifications of its generic fibre. -/
  e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] ((Sigma.desc B).sum' F).obj x
  /-- The quotient transformation over the coefficient subalgebra. -/
  β : Sigma.desc (fun _ : I => H) ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶
    Sum.inl_ (Σ _ : I, C) C ⋙ N
  /-- Finite presentation of the coefficient algebras. -/
  hfp : ∀ x, Algebra.FinitePresentation S (N.obj x)
  /-- Naturality of the generic-fibre identifications. -/
  hn : ∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
      (((Sigma.desc B).sum' F).map a).hom.comp (e x).toAlgHom
  /-- Commutativity of the generic-fibre quotient squares. -/
  hβ : ∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
      (d x).hom.comp (e (.inr ((Sigma.desc (fun _ : I => H)).obj x))).toAlgHom
  /-- Surjectivity of the quotient maps after scalar extension. -/
  hsurj : ∀ x, Function.Surjective
    (Algebra.TensorProduct.lTensor (S := R) R (β.app x).hom)
  /-- Openness of the coefficient-chart transition maps. -/
  hopen : ∀ x y (a : x ⟶ y), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))
  /-- Preservation of the chart pushout squares. -/
  hpush : ∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
    IsPushout (CommRingCat.ofHom (((Sigma.desc B).sum' F).map a).hom.toRingHom)
      (CommRingCat.ofHom (((Sigma.desc B).sum' F).map b).hom.toRingHom)
      (CommRingCat.ofHom (((Sigma.desc B).sum' F).map p).hom.toRingHom)
      (CommRingCat.ofHom (((Sigma.desc B).sum' F).map q).hom.toRingHom) →
    IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
      (CommRingCat.ofHom (N.map b).hom.toRingHom)
      (CommRingCat.ofHom (N.map p).hom.toRingHom)
      (CommRingCat.ofHom (N.map q).hom.toRingHom)

attribute [instance] CoordinateExtensionData.categoryC
  CoordinateExtensionData.algebraSR CoordinateExtensionData.towerSRK

/-- The coordinate and atlas properties after extension of scalars. -/
private def CoordinateExtensionData.Properties
    {K : Type u} [hK : CommRing K] (D : CoordinateExtensionData K) : Prop := by
  cases D with
  | @mk I C hC S R hSR hSRK H F B d N e β hfp hn hβ hsurj hopen hpush =>
      exact
        let NR := N ⋙ tensor_functor S R
        let βR := Functor.whiskerRight β (tensor_functor S R)
        let eR := fun x => tensor_comparison S R (N.obj x)
          (((Sigma.desc B).sum' F).obj x) (e x)
        (∀ x, Algebra.FinitePresentation R (NR.obj x)) ∧
        (∀ x y (a : x ⟶ y), (eR y).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (NR.map a).hom) =
            (((Sigma.desc B).sum' F).map a).hom.comp (eR x).toAlgHom) ∧
        (∀ x : (Σ _ : I, C), (eR (.inl x)).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (βR.app x).hom) =
            (d x).hom.comp (eR (.inr ((Sigma.desc (fun _ : I => H)).obj x))).toAlgHom) ∧
        (∀ x, Function.Surjective (βR.app x).hom) ∧
        (∀ x y (a : x ⟶ y), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom (NR.map a).hom.toRingHom))) ∧
        (∀ (i : I),
          (∀ (x y z : Cᵒᵖ) (a : x ⟶ z) (b : y ⟶ z),
            ∃ (v : Cᵒᵖ) (p : v ⟶ x) (q : v ⟶ y),
              IsPushout (CommRingCat.ofHom ((B i).map a.unop).hom.toRingHom)
                (CommRingCat.ofHom ((B i).map b.unop).hom.toRingHom)
                (CommRingCat.ofHom ((B i).map p.unop).hom.toRingHom)
                (CommRingCat.ofHom ((B i).map q.unop).hom.toRingHom)) →
          ((((Sigma.incl (C := fun _ : I => C) i ⋙ (Sum.inl_ (Σ _ : I, C) C ⋙ NR)).op ⋙ algSpec (.of
            R) ⋙ Over.forget _) ⋙
            Scheme.forget).IsLocallyDirected))

private theorem extend_coordinate_properties
    {K : Type u} [hK : CommRing K] (D : CoordinateExtensionData K) : D.Properties := by
  cases D with
  | @mk I C hC S R hSR hSRK H F B d N e β hfp hn hβ hsurj hopen hpush =>
    let : ∀ x, Algebra.FinitePresentation S (N.obj x) := hfp
    refine ⟨(fun x => inferInstanceAs
      (Algebra.FinitePresentation R (R ⊗[S] N.obj x))), ?_, ?_, ?_, ?_, ?_⟩
    · intro x y a
      exact tensor_comparison_natural S R (e x) (e y) (N.map a)
        (((Sigma.desc B).sum' F).map a) (hn x y a)
    · intro x
      exact tensor_comparison_natural S R
        (e (.inr ((Sigma.desc (fun _ : I => H)).obj x))) (e (.inl x))
        (β.app x) (d x) (hβ x)
    · intro x
      change Function.Surjective (((tensor_functor S R).map (β.app x)).hom)
      rw [tensor_map_hom]
      exact hsurj x
    · intro x y a
      let : IsOpenImmersion ((algSpec (.of S)).map (N.map a).op).left := hopen x y a
      exact tensor_open S R (N.map a)
    · intro i hrefine
      apply @retain_refinements C hC R K (inferInstanceAs (CommRing R)) hK
        (Sigma.incl (C := fun _ : I => C) i ⋙
          (Sum.inl_ (Σ _ : I, C) C ⋙ (N ⋙ tensor_functor S R))) (B i)
      · intro x y z t a b p q h
        let incl : C ⥤ (Σ _ : I, C) ⊕ C :=
          Sigma.incl (C := fun _ : I => C) i ⋙ Sum.inl_ (Σ _ : I, C) C
        exact tensor_pushout S R (N.map (incl.map a)) (N.map (incl.map b))
          (N.map (incl.map p)) (N.map (incl.map q))
          (hpush (.inl ⟨i, x⟩) (.inl ⟨i, y⟩) (.inl ⟨i, z⟩) (.inl ⟨i, t⟩)
            (incl.map a) (incl.map b) (incl.map p) (incl.map q) h)
      · intro x y z a b
        obtain ⟨v, gi, gj, h⟩ := hrefine (op x) (op y) (op z) a.op b.op
        exact ⟨v.unop, gi.unop, gj.unop, h⟩

end SchubertGeometry
