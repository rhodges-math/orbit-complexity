import OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixChartSquares

set_option autoImplicit false

/-! # Coefficient coordinates of closed prefix targets

The quotient coefficients and the mixed Cartesian squares determine one
tensor-extended coordinate diagram. Its spectrum atlas constructs the closed
targets inside the scalar extension of the specified flag model. Both
projections to the coefficient base and to that model are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private scalar_functor
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
open private tensor_functor tensor_comparison tensor_comparison_natural tensor_comparison_original
  tensor_surjective_later tensor_open tensor_pushout tensor_equifibered
  scalar_flag scalar_tower_eq coefficient_triangle
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private quotient_component coordinate_claim construct_coordinate_targets
  ambient_cocone closed_cocone coordinate_inclusion
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
open private target_result stage_properties
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing

private theorem map_stage_data {J : Type*} [Preorder J] (i : J) {P Q : J → Prop}
    (h : ∃ (j : J) (_ : i ≤ j), P j) (f : ∀ j, i ≤ j → P j → Q j) :
    ∃ j, i ≤ j ∧ Q j := by
  obtain ⟨j, hij, hj⟩ := h
  exact ⟨j, hij, f j hij hj⟩

private theorem use_witness {A : Sort*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (f : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact f a ha

private theorem later_surjective {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (i k : CoefficientStage S) (hik : i ≤ k)
    {M N : CommAlgCat.{u} S} (f : M ⟶ N) :
    let _ : Algebra S i.val := (Subalgebra.inclusion i.property.2).toAlgebra
    let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
    Function.Surjective (Algebra.TensorProduct.lTensor (S := i.val) i.val f.hom) →
      Function.Surjective (Algebra.TensorProduct.lTensor (S := k.val) k.val f.hom) := by
  let : Algebra S i.val := (Subalgebra.inclusion i.property.2).toAlgebra
  let : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let : Algebra i.val k.val := (Subalgebra.inclusion hik).toAlgebra
  let : IsScalarTower S i.val k.val := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact tensor_surjective_later S i.val f

private def coefficient_targets
    {Y : Scheme.{u}} {T I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S : Subalgebra ℤ K)
    (N : (Σ _ : I, {s : Finset T // s.Nonempty}) ⊕
      {s : Finset T // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K]
      (((Sigma.desc (fun i => intersectionCoordinates (j i ≫ base)
        (intersectionOpens (fun t => j i ⁻¹ᵁ U t)))).sum' (intersectionCoordinates base
          (intersectionOpens U))).obj x))
    (β : Sigma.desc (fun _ : I => intersectionIndexMap (id : T → T)) ⋙
      (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N)
    (P : Over (Spec (.of S))) (qP : Y ⟶ P.left) (k : CoefficientStage S) : Prop :=
  let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let _ : IsScalarTower S k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let H₀ := intersectionIndexMap (id : T → T)
  let F := intersectionCoordinates base (intersectionOpens U)
  let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U t))
  let A := (Sigma.desc B).sum' F
  let Nₖ := N ⋙ tensor_functor S k.val
  let βₖ := Functor.whiskerRight β (tensor_functor S k.val)
  let eₖ := fun x => tensor_comparison S k.val (N.obj x) (A.obj x) (e x)
  let F₀ := H₀ ⋙ (Sum.inr_ _ _ ⋙ Nₖ)
  let B₀ := fun i => Sigma.incl i ⋙ (Sum.inl_ _ _ ⋙ Nₖ)
  let eF := fun c => eₖ (.inr (H₀.obj c))
  let eB := fun i c => eₖ (.inl ⟨i, c⟩)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S k.val))
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let Pₖ := (scalar_functor κ).obj P
  ∃ (qPk : Y ⟶ Pₖ.left) (hPk : IsPullback qPk base Pₖ.hom ρ)
    (hnF : ∀ c d (a : c ⟶ d), (eF d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (F₀.map a).hom) =
      ((H₀ ⋙ F).map a).hom.comp (eF c).toAlgHom)
    (hnB : ∀ i c d (a : c ⟶ d), (eB i d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((B₀ i).map a).hom) =
      ((B i).map a).hom.comp (eB i c).toAlgHom),
    qPk ≫ pullback.fst κ P.hom = base ≫ ρ ∧
    qPk ≫ pullback.snd κ P.hom = qP ∧
    (∀ x (z : N.obj x), eₖ x ((1 : K) ⊗ₜ[k.val] ((1 : k.val) ⊗ₜ[S] z)) =
      e x ((1 : K) ⊗ₜ[S] z)) ∧
    target_result k.val F₀ B₀ (quotient_component H₀ Nₖ βₖ) (H₀ ⋙ F) B
      eF eB hnF hnB (ambient_cocone base U hU)
      (fun i => closed_cocone (j i) base U hU)
      (fun i => coordinate_inclusion (j i) base U hU) Pₖ qPk hPk
      ⟨k.val, k.property.1, le_rfl⟩ ∧
    ∀ (L : Type u) [CommRing L] [Algebra S L] [Algebra k.val L]
      [IsScalarTower S k.val L],
      let τ := Spec.map (CommRingCat.ofHom (algebraMap k.val L))
      let ζ := Spec.map (CommRingCat.ofHom (algebraMap S L))
      ∃ E : (scalar_functor τ).obj Pₖ ≅ (scalar_functor ζ).obj P,
        E.hom.left ≫ pullback.fst ζ P.hom = pullback.fst τ Pₖ.hom ∧
        E.hom.left ≫ pullback.snd ζ P.hom =
          pullback.snd τ Pₖ.hom ≫ pullback.snd κ P.hom

private theorem targets_from_stage
    {Y : Scheme.{u}} {T I K : Type u} [CommRing K] [Finite T]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤) :
    let C := {s : Finset T // s.Nonempty}
    let H₀ := intersectionIndexMap (id : T → T)
    let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => H₀)
    let F := intersectionCoordinates base (intersectionOpens U)
    let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U
      t))
    let A := (Sigma.desc B).sum' F
    ∀ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N),
      S.FG → (∀ x, Algebra.FinitePresentation S (N.obj x)) →
      (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
        (A.map a).hom.comp (e x).toAlgHom) →
      (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
        ((intersectionCoordinateMap (j x.1) base (fun t => j x.1 ⁻¹ᵁ U t) U id
          (fun _ => le_rfl)).app x.2).hom.comp (e (.inr (H.obj x))).toAlgHom) →
      (∀ x y (a : x ⟶ y), IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))) →
      (∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
        IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
          (CommRingCat.ofHom (A.map b).hom.toRingHom)
          (CommRingCat.ofHom (A.map p).hom.toRingHom)
          (CommRingCat.ofHom (A.map q).hom.toRingHom) →
        IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
          (CommRingCat.ofHom (N.map b).hom.toRingHom)
          (CommRingCat.ofHom (N.map p).hom.toRingHom)
          (CommRingCat.ofHom (N.map q).hom.toRingHom)) →
      ∀ (k : CoefficientStage S),
        let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
        (∀ x, Function.Surjective
          (Algebra.TensorProduct.lTensor (S := k.val) k.val (β.app x).hom)) →
        (∀ i, (Functor.whiskerRight (NatTrans.op (quotient_component H₀ N β i))
          (algSpec (.of S) ⋙ scalar_functor
            (Spec.map (CommRingCat.ofHom (algebraMap S k.val))) ⋙
            Over.forget _)).Equifibered) →
        ∀ (P : Over (Spec (.of S))) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
          [LocallyOfFinitePresentation P.hom] (qP : Y ⟶ P.left),
          IsPullback qP base P.hom
            (Spec.map (CommRingCat.ofHom (algebraMap S K))) →
          coefficient_targets X j base U hU S N e β P qP k := by
  dsimp only
  intro S N e β hS hfp hn hβ hopen hpush k
  let : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  intro hsurj hcart P _ _ _ qP hP
  let : IsScalarTower S k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let C := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  let F := intersectionCoordinates base (intersectionOpens U)
  let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U t))
  let A := (Sigma.desc B).sum' F
  let Nₖ := N ⋙ tensor_functor S k.val
  let βₖ := Functor.whiskerRight β (tensor_functor S k.val)
  let eₖ := fun x => tensor_comparison S k.val (N.obj x) (A.obj x) (e x)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S k.val))
  let Pₖ := (scalar_functor κ).obj P
  let : ∀ x, Algebra.FinitePresentation S (N.obj x) := hfp
  have hfpₖ : ∀ x, Algebra.FinitePresentation k.val (Nₖ.obj x) := fun x =>
    inferInstanceAs (Algebra.FinitePresentation k.val (k.val ⊗[S] N.obj x))
  have hnₖ : ∀ x y (a : x ⟶ y), (eₖ y).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (Nₖ.map a).hom) =
      (A.map a).hom.comp (eₖ x).toAlgHom :=
    fun x y a => tensor_comparison_natural S k.val (e x) (e y) (N.map a) (A.map a) (hn x y a)
  have hβₖ : ∀ x : Σ _ : I, C, (eₖ (.inl x)).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (βₖ.app x).hom) =
      ((intersectionCoordinateMap (j x.1) base (fun t => j x.1 ⁻¹ᵁ U t) U id
        (fun _ => le_rfl)).app x.2).hom.comp
          (eₖ (.inr ((Sigma.desc (fun _ : I => H₀)).obj x))).toAlgHom :=
    fun x => tensor_comparison_natural S k.val _ _ (β.app x) _ (hβ x)
  have hopenₖ : ∀ x y (a : x ⟶ y), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (Nₖ.map a).hom.toRingHom)) := by
    intro x y a
    let : IsOpenImmersion ((algSpec (.of S)).map (N.map a).op).left := hopen x y a
    exact tensor_open S k.val (N.map a)
  have hpushₖ : ∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
      IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
        (CommRingCat.ofHom (A.map b).hom.toRingHom)
        (CommRingCat.ofHom (A.map p).hom.toRingHom)
        (CommRingCat.ofHom (A.map q).hom.toRingHom) →
      IsPushout (CommRingCat.ofHom (Nₖ.map a).hom.toRingHom)
        (CommRingCat.ofHom (Nₖ.map b).hom.toRingHom)
        (CommRingCat.ofHom (Nₖ.map p).hom.toRingHom)
        (CommRingCat.ofHom (Nₖ.map q).hom.toRingHom) :=
    fun x y z t a b p q h => tensor_pushout S k.val
      (N.map a) (N.map b) (N.map p) (N.map q) (hpush x y z t a b p q h)
  have hcartₖ : ∀ i, (Functor.whiskerRight (NatTrans.op (quotient_component H₀ Nₖ βₖ i))
      (algSpec (.of k.val) ⋙ Over.forget _)).Equifibered :=
    fun i => tensor_equifibered S k.val (quotient_component H₀ N β i) (hcart i)
  have hprops := stage_properties S hS P k
  let : CompactSpace Pₖ.left := hprops.2.1
  let : QuasiSeparatedSpace Pₖ.left := hprops.2.2
  let : LocallyOfFinitePresentation Pₖ.hom := hprops.1
  apply use_witness (scalar_flag S k.val P (Over.mk base) qP hP)
  intro qPk hqPk
  have hclosed := construct_coordinate_targets X j base U hU hcover
  dsimp only [coordinate_claim] at hclosed
  have ht := hclosed k.val Nₖ eₖ βₖ k.property.1 hfpₖ hnₖ hβₖ
    hsurj hopenₖ hpushₖ hcartₖ Pₖ qPk hqPk.1 ⟨k.val, k.property.1, le_rfl⟩
  apply use_witness ht
  intro hnF htF
  apply use_witness htF
  intro hnB htB
  refine ⟨qPk, hqPk.1, hnF, hnB, hqPk.2.1, hqPk.2.2,
    (fun x z => tensor_comparison_original S k.val (N.obj x) (A.obj x) (e x) 1 z),
    htB, ?_⟩
  intro L _ _ _ _
  exact scalar_tower_eq κ (Spec.map (CommRingCat.ofHom (algebraMap k.val L)))
    (Spec.map (CommRingCat.ofHom (algebraMap S L))) (coefficient_triangle S k.val) P

/-- Quotient and mixed-square coefficients construct the closed prefix targets
in one scalar extension of the specified ambient model. Tensor cancellation
preserves the coordinate comparisons and both projections of that model. -/
theorem exists_prefix_stage_coordinates
    {Y : Scheme.{u}} {T I K : Type u} [CommRing K] [Finite T] [Finite I]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤) :
    let C := {s : Finset T // s.Nonempty}
    let H₀ := intersectionIndexMap (id : T → T)
    let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => H₀)
    let F := intersectionCoordinates base (intersectionOpens U)
    let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U
      t))
    let A := (Sigma.desc B).sum' F
    ∀ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N),
      S.FG → (∀ x, Algebra.FinitePresentation S (N.obj x)) →
      (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
        (A.map a).hom.comp (e x).toAlgHom) →
      (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
        ((intersectionCoordinateMap (j x.1) base (fun t => j x.1 ⁻¹ᵁ U t) U id
          (fun _ => le_rfl)).app x.2).hom.comp (e (.inr (H.obj x))).toAlgHom) →
      (∀ x y (a : x ⟶ y), IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))) →
      (∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
        IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
          (CommRingCat.ofHom (A.map b).hom.toRingHom)
          (CommRingCat.ofHom (A.map p).hom.toRingHom)
          (CommRingCat.ofHom (A.map q).hom.toRingHom) →
        IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
          (CommRingCat.ofHom (N.map b).hom.toRingHom)
          (CommRingCat.ofHom (N.map p).hom.toRingHom)
          (CommRingCat.ofHom (N.map q).hom.toRingHom)) →
      ∀ (i : CoefficientStage S),
        let _ : Algebra S i.val := (Subalgebra.inclusion i.property.2).toAlgebra
        (∀ x, Function.Surjective
          (Algebra.TensorProduct.lTensor (S := i.val) i.val (β.app x).hom)) →
        ∀ (P : Over (Spec (.of S))) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
          [LocallyOfFinitePresentation P.hom] (qP : Y ⟶ P.left),
          IsPullback qP base P.hom
            (Spec.map (CommRingCat.ofHom (algebraMap S K))) →
          ∃ (k : CoefficientStage S), i ≤ k ∧
            coefficient_targets X j base U hU S N e β P qP k := by
  dsimp only
  intro S N e β hS hfp hn hβ hopen hpush i
  let : Algebra S i.val := (Subalgebra.inclusion i.property.2).toAlgebra
  intro hsurj P _ _ _ qP hP
  let C := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  apply map_stage_data i (exists_prefix_chart_squares X j base U hU S N e β hS hfp hn hβ i)
  intro k hik hk
  let : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  have hsurjₖ : ∀ x : Σ _ : I, C, Function.Surjective
      (Algebra.TensorProduct.lTensor (S := k.val) k.val (β.app x).hom) :=
    fun x => later_surjective S i k hik (β.app x) (hsurj x)
  have hcart : ∀ t, (Functor.whiskerRight (NatTrans.op (quotient_component H₀ N β t))
      (algSpec (.of S) ⋙ scalar_functor
        (Spec.map (CommRingCat.ofHom (algebraMap S k.val))) ⋙ Over.forget _)).Equifibered := by
    intro t s d a
    exact hk t s d a
  exact targets_from_stage X j base U hU hcover S N e β hS hfp hn hβ
    hopen hpush k hsurjₖ hcart P qP hP

end SchubertGeometry
