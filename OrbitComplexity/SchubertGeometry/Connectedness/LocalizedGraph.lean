import Batteries.Tactic.Lint
import OrbitComplexity.GroupActions.Varieties.Contractions.GraphBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedCovers
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageAnchorMaps
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false

/-! # Connected geometric fibres after localizing a cell-curve diagram

Pulling back the pieces, curves and their incidence equations gives a graph
diagram over the localization. The principal-open image cover becomes a
cover there, and the graph yields connected geometric fibres of the target.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FrobeniusSplitting

namespace SchubertGeometry

universe u v

private def unitSection {T : Type*} [Category T] {S : T} (U : Over S)
    [IsIso U.hom] {X : Over S} (f : U ⟶ X) : S ⟶ X.left :=
  (asIso U.hom).inv ≫ f.left

private theorem unitSection_base {T : Type*} [Category T] {S : T} (U : Over S)
    [IsIso U.hom] {X : Over S} (f : U ⟶ X) :
    unitSection U f ≫ X.hom = 𝟙 S := by
  change ((asIso U.hom).inv ≫ f.left) ≫ X.hom = 𝟙 S
  calc
    ((asIso U.hom).inv ≫ f.left) ≫ X.hom =
        (asIso U.hom).inv ≫ (f.left ≫ X.hom) := Category.assoc _ _ _
    _ = (asIso U.hom).inv ≫ U.hom :=
      congrArg (fun t => (asIso U.hom).inv ≫ t) f.w
    _ = 𝟙 S := (asIso U.hom).inv_hom_id

private theorem unitSection_comp {T : Type*} [Category T] {S : T} (U : Over S)
    [IsIso U.hom] {X Y : Over S} (f : U ⟶ X) (g : X ⟶ Y) :
    unitSection U (f ≫ g) = unitSection U f ≫ g.left :=
  (Category.assoc _ _ _).symm

private theorem unit_incidence {T : Type*} [Category T] {S : T} (U : Over S)
    [IsIso U.hom] {X B D : Over S}
    (p : U ⟶ X) (endpoint : U ⟶ B) (piece : X ⟶ D) (bridge : B ⟶ D)
    (h : endpoint ≫ bridge = p ≫ piece) :
    unitSection U endpoint ≫ bridge.left = unitSection U p ≫ piece.left := by
  calc
    unitSection U endpoint ≫ bridge.left = unitSection U (endpoint ≫ bridge) :=
      (unitSection_comp U endpoint bridge).symm
    _ = unitSection U (p ≫ piece) :=
      congrArg (fun f : U ⟶ D => unitSection U f) h
    _ = unitSection U p ≫ piece.left := unitSection_comp U p piece

private theorem anchor_factor {T : Type*} [Category T] {S : T}
    (U X D : Over S) (origin : S ⟶ X.left) (hs : origin ≫ X.hom = 𝟙 S)
    (piece : X ⟶ D) :
    anchorArrow U origin hs piece = anchorArrow U origin hs (𝟙 X) ≫ piece := by
  apply Over.OverMorphism.ext
  change (U.hom ≫ origin) ≫ piece.left = ((U.hom ≫ origin) ≫ 𝟙 X.left) ≫ piece.left
  rw [Category.comp_id]

private theorem mapped_incidence {T : Type*} [Category T] {S S' : T}
    (F : Over S ⥤ Over S') (U : Over S) {X B D : Over S}
    (origin : S ⟶ X.left) (hs : origin ≫ X.hom = 𝟙 S)
    (piece : X ⟶ D) (endpoint : U ⟶ B) (bridge : B ⟶ D)
    (h : endpoint ≫ bridge = anchorArrow U origin hs piece) :
    F.map endpoint ≫ F.map bridge =
      F.map (anchorArrow U origin hs (𝟙 X)) ≫ F.map piece := by
  calc
    F.map endpoint ≫ F.map bridge = F.map (endpoint ≫ bridge) :=
      (F.map_comp endpoint bridge).symm
    _ = F.map (anchorArrow U origin hs piece) :=
      congrArg (fun f : U ⟶ D => F.map f) h
    _ = F.map (anchorArrow U origin hs (𝟙 X) ≫ piece) :=
      congrArg (fun f : U ⟶ D => F.map f) (anchor_factor U X D origin hs piece)
    _ = F.map (anchorArrow U origin hs (𝟙 X)) ≫ F.map piece := F.map_comp _ _

private theorem pullback_unit_iso {T : Type*} [Category T] [HasPullbacks T]
    {S S' : T} (κ : S' ⟶ S) (U : Over S) [IsIso U.hom] :
    IsIso ((Over.pullback κ).obj U).hom := by
  change IsIso (pullback.snd U.hom κ)
  infer_instance

private theorem pullback_map_fst {T : Type*} [Category T] [HasPullbacks T]
    {S S' : T} (κ : S' ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback κ).map f).left ≫ pullback.fst Y.hom κ =
      pullback.fst X.hom κ ≫ f.left := by
  change pullback.lift _ _ _ ≫ pullback.fst Y.hom κ = _
  exact pullback.lift_fst _ _ _

private theorem pullback_map_cartesian {T : Type*} [Category T] [HasPullbacks T]
    {S S' : T} (κ : S' ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom κ) ((Over.pullback κ).map f).left
      f.left (pullback.fst Y.hom κ) := by
  have houter : IsPullback (pullback.fst X.hom κ)
      (((Over.pullback κ).map f).left ≫ ((Over.pullback κ).obj Y).hom)
      (f.left ≫ Y.hom) κ := by
    rw [((Over.pullback κ).map f).w, f.w]
    exact IsPullback.of_hasPullback X.hom κ
  exact houter.of_bot (pullback_map_fst κ f).symm (IsPullback.of_hasPullback Y.hom κ)

private theorem pullback_base_triangle {T : Type*} [Category T] [HasPullbacks T]
    {S S' : T} (κ : S' ⟶ S) (D : Over S) :
    pullback.fst D.hom κ ≫ D.hom = ((Over.pullback κ).obj D).hom ≫ 𝟙 S' ≫ κ := by
  change pullback.fst D.hom κ ≫ D.hom = pullback.snd D.hom κ ≫ 𝟙 S' ≫ κ
  rw [Category.id_comp]
  exact pullback.condition

private theorem scalar_inner_square {T : Type*} [Category T]
    {S A D P Y B : T} {κ : A ⟶ S} {scalar : B ⟶ A}
    {p : P ⟶ D} {dP : P ⟶ A} {d : D ⟶ S} {q : Y ⟶ D} {dY : Y ⟶ B}
    (hinner : IsPullback p dP d κ) (houter : IsPullback q dY d (scalar ≫ κ)) :
    IsPullback
      (hinner.lift q (dY ≫ scalar) (houter.w.trans (Category.assoc _ _ _).symm))
      dY dP scalar := by
  let w := houter.w.trans (Category.assoc _ _ _).symm
  let f := hinner.lift q (dY ≫ scalar) w
  have hf : f ≫ p = q := hinner.lift_fst _ _ _
  have hs : f ≫ dP = dY ≫ scalar := hinner.lift_snd _ _ _
  have ho : IsPullback (f ≫ p) dY d (scalar ≫ κ) := by
    rw [hf]
    exact houter
  exact ho.of_right hs hinner

private theorem pullback_geomConnected {S S' : Scheme.{u}} (κ : S' ⟶ S)
    (X : Over S) (hx : GeometricallyConnected X.hom) :
    GeometricallyConnected ((Over.pullback κ).obj X).hom := by
  change GeometricallyConnected (pullback.snd X.hom κ)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @GeometricallyConnected) (IsPullback.of_hasPullback X.hom κ) hx

/-- A principal-open image cover by pieces with connected geometric fibres,
joined by curves along paths, gives connected geometric fibres after localization. -/
theorem geomConnected_of_localized_graph
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] (D : Over (Spec (.of R)))
    {I : Type v} (rel : I → I → Prop) (root : I)
    (X : I → Over (Spec (.of R))) (piece : ∀ i, X i ⟶ D)
    (origin : ∀ i, Spec (.of R) ⟶ (X i).left)
    (hSection : ∀ i, origin i ≫ (X i).hom = 𝟙 _)
    [∀ i, GeometricallyConnected (X i).hom]
    (U : Over (Spec (.of R))) [IsIso U.hom]
    (B : ∀ i j, rel i j → Over (Spec (.of R)))
    (bridge : ∀ i j (h : rel i j), B i j h ⟶ D)
    (left right : ∀ i j (h : rel i j), U ⟶ B i j h)
    [∀ i j (h : rel i j), GeometricallyConnected (B i j h).hom]
    (hLeft : ∀ i j (h : rel i j), left i j h ≫ bridge i j h =
      anchorArrow U (origin i) (hSection i) (piece i))
    (hRight : ∀ i j (h : rel i j), right i j h ≫ bridge i j h =
      anchorArrow U (origin j) (hSection j) (piece j))
    (hCover : ∀ y : D.left, D.hom y ∈ PrimeSpectrum.basicOpen r →
      ∃ i x, (piece i).left x = y)
    (hPath : ∀ i, Relation.ReflTransGen rel root i) :
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj D).hom := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let F := Over.pullback κ
  let : IsIso (F.obj U).hom := pullback_unit_iso κ U
  let (i : I) : GeometricallyConnected (F.obj (X i)).hom :=
    pullback_geomConnected κ (X i) inferInstance
  let (i j : I) (h : rel i j) : GeometricallyConnected (F.obj (B i j h)).hom :=
    pullback_geomConnected κ (B i j h) inferInstance
  have hCover' : ∀ y : (F.obj D).left, ∃ i x, (F.map (piece i)).left x = y :=
    retainedCover_of_localization r
      (fun i => (X i).left) (fun i => (F.obj (X i)).left)
      (fun i => (piece i).left) (fun i => (F.map (piece i)).left)
      D.hom (𝟙 (Spec (.of A)))
      (fun i => pullback.fst (X i).hom κ) (pullback.fst D.hom κ) (F.obj D).hom
      (pullback_base_triangle κ D) (fun i => pullback_map_cartesian κ (piece i)) hCover
  exact GroupActions.geomConnected_of_graph_diagram (F.obj D).hom rel root
    (fun i => (F.obj (X i)).left) (fun i => (F.obj (X i)).hom)
    (fun i => (F.map (piece i)).left)
    (fun i => unitSection (F.obj U)
      (F.map (anchorArrow U (origin i) (hSection i) (𝟙 (X i)))))
    (fun i => (F.map (piece i)).w)
    (fun i => unitSection_base (F.obj U)
      (F.map (anchorArrow U (origin i) (hSection i) (𝟙 (X i)))))
    (fun i j h => (F.obj (B i j h)).left) (fun i j h => (F.obj (B i j h)).hom)
    (fun i j h => (F.map (bridge i j h)).left)
    (fun i j h => unitSection (F.obj U) (F.map (left i j h)))
    (fun i j h => unitSection (F.obj U) (F.map (right i j h)))
    (fun i j h => (F.map (bridge i j h)).w)
    (fun i j h => unit_incidence (F.obj U)
      (F.map (anchorArrow U (origin i) (hSection i) (𝟙 (X i))))
      (F.map (left i j h)) (F.map (piece i)) (F.map (bridge i j h))
      (mapped_incidence F U (origin i) (hSection i) (piece i)
        (left i j h) (bridge i j h) (hLeft i j h)))
    (fun i j h => unit_incidence (F.obj U)
      (F.map (anchorArrow U (origin j) (hSection j) (𝟙 (X j))))
      (F.map (right i j h)) (F.map (piece j)) (F.map (bridge i j h))
      (mapped_incidence F U (origin j) (hSection j) (piece j)
        (right i j h) (bridge i j h) (hRight i j h))) hCover' hPath

end SchubertGeometry
