import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AppendEndpointStage
import OrbitComplexity.SchubertGeometry.Connectedness.AppendCellModels
import OrbitComplexity.GroupActions.Varieties.GeometricCover
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

set_option autoImplicit false

/-! # Connectedness of appended endpoints from their Schubert cells

The retained cell products transfer the constructed Weyl-fibre
connectedness to every cell inverse image. The image cover then proves
connectedness of the specified endpoint under arbitrary field probes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open FrobeniusSplitting GroupActions Opposite

namespace SchubertGeometry

universe u v

attribute [local instance] Over.cartesianMonoidalCategory
private def fibre_model {B : Scheme.{u}} {F Q : Over B}
    (π : F ⟶ Q) (b : Over.mk (𝟙 B) ⟶ Q) : Over B :=
  Over.mk (pullback.snd π.left b.left)

private theorem scalar_arrow_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    IsPullback (chosenScalarArrow κ f).left (pullback.snd κ X.hom)
      (pullback.snd κ Y.hom) f.left := by
  have hf : (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom := by
    have hw := (chosenScalarArrow κ f).w
    change (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom at hw
    exact hw
  have h : IsPullback ((chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom)
      (pullback.snd κ X.hom) κ (f.left ≫ Y.hom) := by
    rw [hf, f.w]
    exact IsPullback.of_hasPullback κ X.hom
  exact h.of_right (chosenScalarArrow_snd κ f) (IsPullback.of_hasPullback κ Y.hom)

private theorem scalar_identity {B T : Scheme.{u}} (κ : T ⟶ B) (X : Over B) :
    chosenScalarArrow κ (𝟙 X) = 𝟙 (Over.mk (pullback.fst κ X.hom)) := by
  apply (Over.forget T).map_injective
  change (chosenScalarArrow κ (𝟙 X)).left = 𝟙 (pullback κ X.hom)
  apply pullback.hom_ext
  · exact (chosenScalarArrow κ (𝟙 X)).w.trans (Category.id_comp _).symm
  · rw [chosenScalarArrow_snd]
    exact (Category.comp_id (pullback.snd κ X.hom)).trans
      (Category.id_comp (pullback.snd κ X.hom)).symm

private theorem scalar_composition {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chosenScalarArrow κ (f ≫ g) = chosenScalarArrow κ f ≫ chosenScalarArrow κ g := by
  apply (Over.forget T).map_injective
  apply pullback.hom_ext
  · exact (chosenScalarArrow κ (f ≫ g)).w.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (chosenScalarArrow κ f).left ≫ k)
          (chosenScalarArrow κ g).w).trans (chosenScalarArrow κ f).w)).symm
  · calc
      (chosenScalarArrow κ (f ≫ g)).left ≫ pullback.snd κ Z.hom =
          pullback.snd κ X.hom ≫ (f ≫ g).left := chosenScalarArrow_snd κ (f ≫ g)
      _ = (pullback.snd κ X.hom ≫ f.left) ≫ g.left := (Category.assoc _ _ _).symm
      _ = ((chosenScalarArrow κ f).left ≫ pullback.snd κ Y.hom) ≫ g.left :=
        congrArg (fun k => k ≫ g.left) (chosenScalarArrow_snd κ f).symm
      _ = (chosenScalarArrow κ f).left ≫ (pullback.snd κ Y.hom ≫ g.left) :=
        Category.assoc _ _ _
      _ = (chosenScalarArrow κ f).left ≫
          ((chosenScalarArrow κ g).left ≫ pullback.snd κ Z.hom) :=
        congrArg (fun k => (chosenScalarArrow κ f).left ≫ k)
          (chosenScalarArrow_snd κ g).symm
      _ = ((chosenScalarArrow κ f).left ≫ (chosenScalarArrow κ g).left) ≫
          pullback.snd κ Z.hom := (Category.assoc _ _ _).symm

private def scalar_functor {B T : Scheme.{u}} (κ : T ⟶ B) : Over B ⥤ Over T where
  obj X := Over.mk (pullback.fst κ X.hom)
  map f := chosenScalarArrow κ f
  map_id X := scalar_identity κ X
  map_comp f g := scalar_composition κ f g

private theorem scalar_closed {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedImmersion (chosenScalarArrow κ f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (scalar_arrow_cartesian κ f).flip inferInstance

private theorem scalar_arrow_fst {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom = pullback.fst κ X.hom := by
  have h := (chosenScalarArrow κ f).w
  change (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom = pullback.fst κ X.hom at h
  exact h

private def scalar_pullback_iso {B T : Scheme.{u}} (κ : T ⟶ B) :
    scalar_functor κ ≅ Over.pullback κ :=
  NatIso.ofComponents
    (fun X => Over.isoMk (pullbackSymmetry κ X.hom)
      (pullbackSymmetry_hom_comp_snd κ X.hom))
    (fun {X Y} f => by
      apply (Over.forget T).map_injective
      change (chosenScalarArrow κ f).left ≫ (pullbackSymmetry κ Y.hom).hom =
        (pullbackSymmetry κ X.hom).hom ≫ ((Over.pullback κ).map f).left
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc,
          pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_fst_assoc,
          pullback.lift_fst, chosenScalarArrow_snd]
      · simp only [Over.pullback_map_left, Category.assoc,
          pullbackSymmetry_hom_comp_snd, pullback.lift_snd, scalar_arrow_fst])

private instance scalar_preserves_limit {B T : Scheme.{u}} (κ : T ⟶ B)
    {I : Type*} [Category I] (D : I ⥤ Over B) : PreservesLimit D (scalar_functor κ) :=
  preservesLimit_of_natIso D (scalar_pullback_iso κ).symm

private def cell_source {B : Scheme.{u}} {N F C : Over B}
    (n : N ⟶ F) (c : C ⟶ F) : Over B :=
  Over.mk (pullback.snd n.left c.left ≫ C.hom)

private def cell_projection {B : Scheme.{u}} {N F C : Over B}
    (n : N ⟶ F) (c : C ⟶ F) : cell_source n c ⟶ C :=
  Over.homMk (pullback.snd n.left c.left) rfl

private def cell_first {B : Scheme.{u}} {N F C : Over B}
    (n : N ⟶ F) (c : C ⟶ F) : cell_source n c ⟶ N :=
  Over.homMk (pullback.fst n.left c.left) (by
    calc
      pullback.fst n.left c.left ≫ N.hom =
          (pullback.fst n.left c.left ≫ n.left) ≫ F.hom :=
        (congrArg (fun f => pullback.fst n.left c.left ≫ f) n.w.symm).trans
          (Category.assoc _ _ _).symm
      _ = (pullback.snd n.left c.left ≫ c.left) ≫ F.hom :=
        congrArg (fun f => f ≫ F.hom) (pullback.condition (f := n.left) (g := c.left))
      _ = pullback.snd n.left c.left ≫ C.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f => pullback.snd n.left c.left ≫ f) c.w))

private theorem iso_cancel_gc {X Y Z : Scheme.{u}} (E : X ≅ Y)
    (f : Y ⟶ Z) (g : X ⟶ Z) (he : E.hom ≫ f = g)
    (h : GeometricallyConnected g) : GeometricallyConnected f := by
  have hcomp : GeometricallyConnected (E.hom ≫ f) := he.symm ▸ h
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) E.hom f).mp hcomp

private theorem product_triangle {B : Scheme.{u}} {P C W : Over B}
    (E : P ≅ C ⊗ W) (p : P ⟶ C) (he : E.hom ≫ fst C W = p) :
    let Q := (Over.forget B).mapIso E ≪≫ pullbackSymmetry C.hom W.hom
    Q.hom ≫ pullback.snd W.hom C.hom = p.left := by
  intro Q
  change (E.hom.left ≫ (pullbackSymmetry C.hom W.hom).hom) ≫
    pullback.snd W.hom C.hom = p.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => E.hom.left ≫ f)
      (pullbackSymmetry_hom_comp_snd C.hom W.hom)).trans (congrArg Over.Hom.left he))

private theorem retained_cell_gc {B T : Scheme.{u}} (κ : T ⟶ B)
    {N F C : Over B} (n : N ⟶ F) (c : C ⟶ F) (b : Over.mk (𝟙 B) ⟶ F)
    (E : (scalar_functor κ).obj (cell_source n c) ≅
      (scalar_functor κ).obj (C ⊗ fibre_model n b))
    (he : E.hom ≫ chosenScalarArrow κ (fst C (fibre_model n b)) =
      chosenScalarArrow κ (cell_projection n c))
    [GeometricallyConnected ((scalar_functor κ).obj (fibre_model n b)).hom] :
    GeometricallyConnected
      (pullback.snd (chosenScalarArrow κ n).left (chosenScalarArrow κ c).left) := by
  let Fκ := scalar_functor κ
  let W := fibre_model n b
  let H : Fκ.obj (cell_source n c) ≅ Fκ.obj C ⊗ Fκ.obj W :=
    E ≪≫ prodComparisonIso Fκ C W
  have hproj : (prodComparisonIso Fκ C W).hom ≫ fst (Fκ.obj C) (Fκ.obj W) =
      Fκ.map (fst C W) := by
    rw [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst]
  have hmap : Fκ.map (fst C W) = chosenScalarArrow κ (fst C W) := rfl
  have hH : H.hom ≫ fst (Fκ.obj C) (Fκ.obj W) =
      chosenScalarArrow κ (cell_projection n c) := by
    change (E.hom ≫ (prodComparisonIso Fκ C W).hom) ≫
      fst (Fκ.obj C) (Fκ.obj W) = _
    exact (Category.assoc E.hom (prodComparisonIso Fκ C W).hom
      (fst (Fκ.obj C) (Fκ.obj W))).trans
        ((congrArg (fun f : Fκ.obj (C ⊗ W) ⟶ Fκ.obj C => E.hom ≫ f)
          (hproj.trans hmap)).trans he)
  let Q := (Over.forget T).mapIso H ≪≫ pullbackSymmetry (Fκ.obj C).hom (Fκ.obj W).hom
  have hlocal : GeometricallyConnected (chosenScalarArrow κ (cell_projection n c)).left :=
    endpoint_cell_product_gc (Fκ.obj W).hom (Fκ.obj C).hom
      (chosenScalarArrow κ (cell_projection n c)).left Q (product_triangle H _ hH)
  have hsource : IsPullback (cell_first n c) (cell_projection n c) n c :=
    IsPullback.of_map_of_faithful (Over.forget B) (IsPullback.of_hasPullback n.left c.left)
  have hscalar := (Over.forget T).map_isPullback (Fκ.map_isPullback hsource)
  exact iso_cancel_gc hscalar.isoPullback
    (pullback.snd (chosenScalarArrow κ n).left (chosenScalarArrow κ c).left)
    (chosenScalarArrow κ (cell_projection n c)).left hscalar.isoPullback_hom_snd hlocal

private theorem gc_pullback_replace {N C F : Scheme.{u}}
    {f f' : N ⟶ F} {g g' : C ⟶ F} (hf : f = f') (hg : g = g')
    (h : GeometricallyConnected (pullback.snd f g)) :
    GeometricallyConnected (pullback.snd f' g') := by
  subst f'
  subst g'
  exact h

private theorem gc_pullback_comp_mono {N C Y F : Scheme.{u}}
    (f : N ⟶ Y) (g : C ⟶ Y) (j : Y ⟶ F) [Mono j]
    (h : GeometricallyConnected (pullback.snd (f ≫ j) (g ≫ j))) :
    GeometricallyConnected (pullback.snd f g) := by
  let hp := IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f g j)
  have hcomp : GeometricallyConnected
      (hp.isoPullback.hom ≫ pullback.snd (f ≫ j) (g ≫ j)) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
      hp.isoPullback.hom (pullback.snd (f ≫ j) (g ≫ j))).mpr h
  have he : hp.isoPullback.hom ≫ pullback.snd (f ≫ j) (g ≫ j) =
      pullback.snd f g := hp.isoPullback_hom_snd
  exact he ▸ hcomp

private theorem field_fibre_connected {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyConnected f] (L : Type u) [Field L] (y : Spec (.of L) ⟶ Y) :
    ConnectedSpace (pullback f y : Scheme.{u}) := by
  let : GeometricallyConnected (pullback.snd f y) := inferInstance
  exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)

private def endpoint_result {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {N Z : Over (Spec (.of S))} (m : N ⟶ Z) (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k),
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    let mk := chosenScalarArrow κ m
    (mk.left ≫ (stageScalarModel S Z.hom k).hom = (stageScalarModel S N.hom k).hom) ∧
    (mk.left ≫ pullback.snd κ Z.hom = pullback.snd κ N.hom ≫ m.left) ∧
    GeometricallyConnected mk.left ∧
    ∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S Z.hom k).left),
      ConnectedSpace (pullback mk.left y : Scheme.{u})

private theorem finish_cell_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {N Z F : Over (Spec (.of S))} (m : N ⟶ Z)
    (j : Z ⟶ F) [IsClosedImmersion j.left]
    (C : J → Over (Spec (.of S))) (c : ∀ r, C r ⟶ Z)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (start s k : CoefficientStage S) (hs : start ≤ s) (hsk : s ≤ k)
    (hW : ∀ r, GeometricallyConnected
      (stageScalarModel S (fibre_model (m ≫ j) (b r)).hom s).hom)
    (E : ∀ r, stageScalarModel S (cell_source (m ≫ j) (c r ≫ j)).hom k ≅
      stageScalarModel S (C r ⊗ fibre_model (m ≫ j) (b r)).hom k)
    (he : ∀ r, (E r).hom ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (fst (C r) (fibre_model (m ≫ j) (b r))) =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
          (cell_projection (m ≫ j) (c r ≫ j)))
    (hcover : ∀ y : (stageScalarModel S Z.hom k).left, ∃ r,
      y ∈ Set.range (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
          (c r)).left) : endpoint_result S m start := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let mk := chosenScalarArrow κ m
  let jk := chosenScalarArrow κ j
  let : IsClosedImmersion jk.left := scalar_closed κ j
  have hlocal (r : J) : GeometricallyConnected (pullback.snd mk.left
      (chosenScalarArrow κ (c r)).left) := by
    let : GeometricallyConnected
        ((scalar_functor κ).obj (fibre_model (m ≫ j) (b r))).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (stageScalarCartesian S (fibre_model (m ≫ j) (b r)).hom hsk) (hW r)
    have hraw := retained_cell_gc κ (m ≫ j) (c r ≫ j) (b r) (E r) (he r)
    have hcomp := gc_pullback_replace
      (congrArg Over.Hom.left (scalar_composition κ m j))
      (congrArg Over.Hom.left (scalar_composition κ (c r) j)) hraw
    exact gc_pullback_comp_mono mk.left (chosenScalarArrow κ (c r)).left jk.left hcomp
  let : GeometricallyConnected mk.left := geometricallyConnected_of_cover mk.left
    (fun r => (stageScalarModel S (C r).hom k).left)
    (fun r => (chosenScalarArrow κ (c r)).left) hcover hlocal
  exact ⟨k, le_trans hs hsk, mk.w, chosenScalarArrow_snd κ m, inferInstance,
    field_fibre_connected mk.left⟩

private theorem bind_weyl_result {A I J : Type*} [Preorder I]
    {P₁ P₂ P₃ : A → Prop} {B : I → Type*}
    {Q₁ : ∀ i, B i → Prop} {Q₂ : A → ∀ i, B i → Prop}
    {C D : I → J → Prop} {R : Prop} (start : I)
    (h : ∃ a, P₁ a ∧ P₂ a ∧ P₃ a ∧
      ∃ (i : I) (_ : start ≤ i) (b : B i), Q₁ i b ∧ Q₂ a i b ∧ ∀ j, C i j ∧ D i j)
    (next : ∀ (i : I) (_ : start ≤ i), (∀ j, C i j) → R) : R := by
  obtain ⟨a, _ha₁, _ha₂, _ha₃, i, hi, b, _hb₁, _hb₂, hCD⟩ := h
  exact next i hi (fun j => (hCD j).1)

private theorem bind_cell_result {A I : Type*} [Preorder I] {B : I → Type*}
    {P₁ P₂ : A → ∀ i, B i → Prop} {P₃ P₄ : ∀ i, B i → Prop}
    {R : Prop} (start : I)
    (h : ∃ (a : A) (i : I) (_ : start ≤ i) (b : B i),
      P₁ a i b ∧ P₂ a i b ∧ P₃ i b ∧ P₄ i b)
    (next : ∀ (i : I) (_ : start ≤ i) (b : B i), P₃ i b → R) : R := by
  obtain ⟨a, i, hi, b, _hb₁, _hb₂, hb₃, _hb₄⟩ := h
  exact next i hi b hb₃

/-- The finite cell comparisons and their scalar image cover prove connectedness
of the specified appended endpoint, preserving its two scalar projections. -/
theorem exists_append_cell_connected
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (v : G.weylGroup) (i : G.rootBase.support)
    {J : Type v} [Fintype J] (x : J → G.weylGroup)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (hx : ∀ r, WeylBruhatLE G.rootBase (x r)
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    {N A Y Z F Q : Over (Spec (.of S))}
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom]
    [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom]
    [LocallyOfFinitePresentation Q.hom]
    (f : A ⟶ Y) [IsProper f.left] [GeometricallyConnected f.left]
    (j : Y ⟶ F) [IsClosedImmersion j.left]
    (m : N ⟶ Z) (z : Z ⟶ F) [IsClosedImmersion z.left] (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (C : J → Over (Spec (.of S))) [∀ r, CompactSpace (C r).left]
    [∀ r, LocallyOfFinitePresentation (C r).hom] (c : ∀ r, C r ⟶ Z)
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (qC : ∀ r, (schubertCell G (x r)).scheme ⟶ (C r).left)
    (hN : IsPullback qN (bsdhToSpec G (word ++ [i])) N.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hA : IsPullback qA (bsdhToSpec G word) A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hQ : IsPullback qQ (partialFlagVariety G {i}).toSpec Q.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hC : ∀ r, IsPullback (qC r) (schubertCell G (x r)).toSpec (C r).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ (m ≫ z).left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ (f ≫ j).left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (hb : ∀ r, (weylFlagPoint G (x r)).val ≫ qF =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ (b r).left)
    (hc : ∀ r, (schubertCellInclusion G (x r)).left ≫ qF = qC r ≫ (c r ≫ z).left)
    (hcover : ∀ k : CoefficientStage S,
      ∀ y : (stageScalarModel S Z.hom k).left, ∃ r,
        y ∈ Set.range (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
            (c r)).left)
    (start : CoefficientStage S) : endpoint_result S m start := by
  let : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  apply bind_weyl_result start
    (exists_append_weyl_connected S hS G word v i x hv hx f j (m ≫ z) π b
      qN qA qY qF qQ hN hA hY hF hQ hn ha hj hπ hb start)
  intro s hs hW
  apply bind_cell_result s
    (@exists_bsdh_cell_stages K _ _ _ S hS G (word ++ [i]) J _ x N F
      inferInstance inferInstance inferInstance C (fun r => inferInstance) (fun r => inferInstance)
      (m ≫ z) (fun r => c r ≫ z) b qN qF qC hN hF hC hn.symm hc hb s)
  intro k hsk E he
  exact finish_cell_stage S m z C c b start s k hs hsk hW E he (hcover k)

-- GAP: C6-STAGE. Produce these cell maps and their scalar image covers from
-- the retained Schubert cell cover, and the flag sections from the selected
-- Schubert Weyl points; then iterate the endpoint step on the reduced word.

end SchubertGeometry
