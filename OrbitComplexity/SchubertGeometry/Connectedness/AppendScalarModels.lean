import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.ProjectiveCurveRetention
import OrbitComplexity.SchubertGeometry.Connectedness.ScalarArrowSquares
import OrbitComplexity.SchubertGeometry.Connectedness.EndpointInduction
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Scalar extensions and intersections of append fibres -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite

namespace SchubertGeometry

universe u v

private theorem scalar_identity {B T : Scheme.{u}} (κ : T ⟶ B) (X : Over B) :
    chosenScalarArrow κ (𝟙 X) = 𝟙 (Over.mk (pullback.fst κ X.hom)) := by
  apply (Over.forget T).map_injective
  change (chosenScalarArrow κ (𝟙 X)).left =
    𝟙 (pullback κ X.hom)
  apply pullback.hom_ext
  · exact (chosenScalarArrow κ (𝟙 X)).w.trans (Category.id_comp _).symm
  · rw [chosenScalarArrow_snd]
    exact (Category.comp_id (pullback.snd κ X.hom)).trans
      (Category.id_comp (pullback.snd κ X.hom)).symm

/-- Scalar extension respects composition of morphisms over the base. -/
theorem appendModel_composition {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chosenScalarArrow κ (f ≫ g) = chosenScalarArrow κ f ≫ chosenScalarArrow κ g := by
  apply (Over.forget T).map_injective
  change (chosenScalarArrow κ (f ≫ g)).left =
    (chosenScalarArrow κ f ≫ chosenScalarArrow κ g).left
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

/-- The scalar-extension functor on schemes over a fixed base. -/
def scalarFunctor {B T : Scheme.{u}} (κ : T ⟶ B) : Over B ⥤ Over T where
  obj X := Over.mk (pullback.fst κ X.hom)
  map f := chosenScalarArrow κ f
  map_id X := scalar_identity κ X
  map_comp f g := appendModel_composition κ f g

/-- An isomorphism over the base preserves geometric connectedness. -/
theorem appendModel_iso_connected {B : Scheme.{u}} {X Y : Over B}
    (E : X ≅ Y) (h : GeometricallyConnected Y.hom) : GeometricallyConnected X.hom := by
  let : GeometricallyConnected Y.hom := h
  have h' : GeometricallyConnected (E.hom.left ≫ Y.hom) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) E.hom.left Y.hom).mpr inferInstance
  exact E.hom.w ▸ h'

/-- Scalar extension preserves geometric connectedness of a morphism. -/
theorem appendModel_arrow_connected {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) [GeometricallyConnected f.left] :
    GeometricallyConnected (chosenScalarArrow κ f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (scalarArrow_cartesian κ f).flip inferInstance

/-- Scalar extension preserves properness of a morphism. -/
theorem appendModel_arrow_proper {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) [IsProper f.left] :
    IsProper (chosenScalarArrow κ f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (scalarArrow_cartesian κ f).flip inferInstance

/-- The scalar extension of a section commutes with a target morphism. -/
theorem appendModel_section_naturality {B T : Scheme.{u}} (κ : T ⟶ B)
    {F Q : Over B} (π : F ⟶ Q) (b : Over.mk (𝟙 B) ⟶ F) :
    scalarSection κ F.hom b.left b.w ≫ (chosenScalarArrow κ π).left =
      scalarSection κ Q.hom (b ≫ π).left (b ≫ π).w := by
  apply pullback.hom_ext
  · calc
      (scalarSection κ F.hom b.left b.w ≫ (chosenScalarArrow κ π).left) ≫
          pullback.fst κ Q.hom =
          scalarSection κ F.hom b.left b.w ≫ pullback.fst κ F.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f => scalarSection κ F.hom b.left b.w ≫ f)
            (chosenScalarArrow κ π).w)
      _ = 𝟙 T := pullback.lift_fst _ _ _
      _ = scalarSection κ Q.hom (b ≫ π).left (b ≫ π).w ≫
          pullback.fst κ Q.hom := (pullback.lift_fst _ _ _).symm
  · calc
      (scalarSection κ F.hom b.left b.w ≫ (chosenScalarArrow κ π).left) ≫
          pullback.snd κ Q.hom =
          scalarSection κ F.hom b.left b.w ≫ (pullback.snd κ F.hom ≫ π.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f => scalarSection κ F.hom b.left b.w ≫ f)
            (chosenScalarArrow_snd κ π))
      _ = (scalarSection κ F.hom b.left b.w ≫ pullback.snd κ F.hom) ≫ π.left :=
        (Category.assoc _ _ _).symm
      _ = (κ ≫ b.left) ≫ π.left :=
        congrArg (fun f => f ≫ π.left) (pullback.lift_snd _ _ _)
      _ = κ ≫ (b ≫ π).left := Category.assoc _ _ _
      _ = scalarSection κ Q.hom (b ≫ π).left (b ≫ π).w ≫
          pullback.snd κ Q.hom := (pullback.lift_snd _ _ _).symm

/-- The scalar extension of a point represented by a section. -/
def scalarPoint {B T : Scheme.{u}} (κ : T ⟶ B)
    {F : Over B} (b : Over.mk (𝟙 B) ⟶ F) :
    Over.mk (𝟙 T) ⟶ (scalarFunctor κ).obj F :=
  Over.homMk (scalarSection κ F.hom b.left b.w) (pullback.lift_fst _ _ _)

/-- A Cartesian curve fibre remains Cartesian after scalar extension. -/
theorem appendModel_curve_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {C F Q : Over B} (c : C ⟶ F) (π : F ⟶ Q)
    (b : Over.mk (𝟙 B) ⟶ Q) (h : IsPullback c.left C.hom π.left b.left) :
    IsPullback (chosenScalarArrow κ c).left (pullback.fst κ C.hom)
      (chosenScalarArrow κ π).left (scalarSection κ Q.hom b.left b.w) := by
  let d := (chosenScalarArrow κ c).left
  let a := pullback.fst κ C.hom
  let s := scalarSection κ Q.hom b.left b.w
  have hd : (d ≫ pullback.snd κ F.hom) ≫ π.left = a ≫ (κ ≫ b.left) := by
    calc
      (d ≫ pullback.snd κ F.hom) ≫ π.left =
          (pullback.snd κ C.hom ≫ c.left) ≫ π.left :=
        congrArg (fun k => k ≫ π.left) (chosenScalarArrow_snd κ c)
      _ = pullback.snd κ C.hom ≫ (C.hom ≫ b.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => pullback.snd κ C.hom ≫ k) h.w)
      _ = (pullback.snd κ C.hom ≫ C.hom) ≫ b.left := (Category.assoc _ _ _).symm
      _ = (a ≫ κ) ≫ b.left := congrArg (fun k => k ≫ b.left)
        (pullback.condition (f := κ) (g := C.hom)).symm
      _ = a ≫ (κ ≫ b.left) := Category.assoc _ _ _
  have hc : d ≫ (chosenScalarArrow κ π).left = a ≫ s :=
    scalarFibre_lift_triangle d (chosenScalarArrow κ π).left a s
      (pullback.snd κ F.hom) (pullback.snd κ Q.hom) (pullback.fst κ Q.hom)
      π.left κ b.left Q.hom (IsPullback.of_hasPullback κ Q.hom).flip
      (chosenScalarArrow_snd κ π) hd (pullback.lift_snd _ _ _)
      (chosenScalarArrow κ c ≫ chosenScalarArrow κ π).w (pullback.lift_fst _ _ _)
  have hout : IsPullback (d ≫ pullback.snd κ F.hom) a π.left
      (s ≫ pullback.snd κ Q.hom) := by
    rw [chosenScalarArrow_snd κ c, show s ≫ pullback.snd κ Q.hom = κ ≫ b.left from
      pullback.lift_snd _ _ _]
    exact (IsPullback.of_hasPullback κ C.hom).flip.paste_horiz h
  exact hout.of_right hc (scalarArrow_cartesian κ π).flip

/-- The canonical isomorphism for two successive scalar extensions. -/
def scalarTowerIso {B T U : Scheme.{u}} (ζ : U ⟶ T) (κ : T ⟶ B)
    (X : Over B) :
    (scalarFunctor ζ).obj ((scalarFunctor κ).obj X) ≅
      (scalarFunctor (ζ ≫ κ)).obj X :=
  ((IsPullback.of_hasPullback ζ (pullback.fst κ X.hom)).flip.paste_horiz
    (IsPullback.of_hasPullback κ X.hom).flip).flip.isoOverPullback

/-- Equal base maps induce the canonical comparison of scalar extensions. -/
def scalarMapEq {B T : Scheme.{u}} {κ ζ : T ⟶ B} (h : κ = ζ)
    (X : Over B) : (scalarFunctor κ).obj X ≅ (scalarFunctor ζ).obj X :=
  eqToIso (congrArg (fun f => (scalarFunctor f).obj X) h)

/-- A composite coefficient inclusion induces the corresponding affine triangle. -/
theorem appendModel_spec_triangle {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (h : R →+* B) (hgf : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp]
  exact congrArg (fun k : R →+* B => Spec.map (CommRingCat.ofHom k)) hgf

/-- The fibre product of two models over their common target. -/
def intersectionModel {B : Scheme.{u}} {C Y F : Over B}
    (c : C ⟶ F) (j : Y ⟶ F) : Over B :=
  Over.mk (pullback.fst c.left j.left ≫ C.hom)

/-- The first projection of an intersection model. -/
def intersectionFst {B : Scheme.{u}} {C Y F : Over B}
    (c : C ⟶ F) (j : Y ⟶ F) : intersectionModel c j ⟶ C :=
  Over.homMk (pullback.fst c.left j.left) rfl

/-- The second projection of an intersection model. -/
def intersectionSnd {B : Scheme.{u}} {C Y F : Over B}
    (c : C ⟶ F) (j : Y ⟶ F) : intersectionModel c j ⟶ Y :=
  Over.homMk (pullback.snd c.left j.left) (by
    calc
      pullback.snd c.left j.left ≫ Y.hom =
          (pullback.snd c.left j.left ≫ j.left) ≫ F.hom :=
        (congrArg (fun f => pullback.snd c.left j.left ≫ f) j.w.symm).trans
          (Category.assoc _ _ _).symm
      _ = (pullback.fst c.left j.left ≫ c.left) ≫ F.hom :=
        congrArg (fun f => f ≫ F.hom) (pullback.condition (f := c.left) (g := j.left)).symm
      _ = pullback.fst c.left j.left ≫ C.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f => pullback.fst c.left j.left ≫ f) c.w))

/-- Scalar extension commutes with the intersection of two models. -/
def scalarIntersectionIso {B T : Scheme.{u}} (κ : T ⟶ B)
    {C Y F : Over B} (c : C ⟶ F) (j : Y ⟶ F) :
    intersectionModel (chosenScalarArrow κ c) (chosenScalarArrow κ j) ≅
      (scalarFunctor κ).obj (intersectionModel c j) := by
  let h := paired_model_scalar_pullback κ
    (pullback.fst κ C.hom) (pullback.fst κ Y.hom) (pullback.fst κ F.hom)
    C.hom Y.hom F.hom (chosenScalarArrow κ c).left (chosenScalarArrow κ j).left
    c.left j.left (chosenScalarArrow κ c).w (chosenScalarArrow κ j).w c.w j.w
    (pullback.snd κ C.hom) (pullback.snd κ Y.hom) (pullback.snd κ F.hom)
    (IsPullback.of_hasPullback κ C.hom).flip
    (IsPullback.of_hasPullback κ Y.hom).flip
    (IsPullback.of_hasPullback κ F.hom).flip
    (chosenScalarArrow_snd κ c) (chosenScalarArrow_snd κ j)
  exact h.1.flip.isoOverPullback

/-- The append correspondence preserves geometric connectedness over a point. -/
theorem appendModel_point_connected {B : Scheme.{u}} {N A Y F Q C : Over B}
    (f : A ⟶ Y) (j : Y ⟶ F) [IsProper f.left] [GeometricallyConnected f.left]
    (n : N ⟶ F) (π : F ⟶ Q) (d : N ⟶ A)
    (b : Over.mk (𝟙 B) ⟶ F) (c : C ⟶ F)
    (hg : IsPullback d.left n.left ((f ≫ j).left ≫ π.left) π.left)
    (hc : IsPullback c.left C.hom π.left (b ≫ π).left)
    [GeometricallyConnected (intersectionModel c j).hom] :
    GeometricallyConnected (fibreModel n b).hom := by
  let I := intersectionModel c j
  let pC := intersectionFst c j
  let pY := intersectionSnd c j
  let hI : IsPullback pC pY c j :=
    IsPullback.of_map_of_faithful (Over.forget B) (IsPullback.of_hasPullback c.left j.left)
  let V : Over B := pullback f pY
  let hV := IsPullback.of_hasPullback f pY
  have hVs : IsPullback (pullback.fst f pY).left (pullback.snd f pY).left
      f.left pY.left := (Over.forget B).map_isPullback hV
  let : IsProper (pullback.snd f pY).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hVs inferInstance
  let : GeometricallyConnected (pullback.snd f pY).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hVs inferInstance
  have hVG : GeometricallyConnected V.hom := by
    have hcomp := endpoint_proper_gc_comp (pullback.snd f pY).left I.hom
    exact (pullback.snd f pY).w ▸ hcomp
  let pN := fibreProjection n b
  let pB : fibreModel n b ⟶ Over.mk (𝟙 B) :=
    Over.homMk (fibreModel n b).hom (Category.comp_id _)
  have hW : IsPullback pN pB n b :=
    IsPullback.of_map_of_faithful (Over.forget B) (IsPullback.of_hasPullback n.left b.left)
  have hg' : IsPullback d n ((f ≫ j) ≫ π) π :=
    IsPullback.of_map_of_faithful (Over.forget B) hg
  let t : C ⟶ Over.mk (𝟙 B) := Over.homMk C.hom (Category.comp_id _)
  have hc' : IsPullback c t π (b ≫ π) :=
    IsPullback.of_map_of_faithful (Over.forget B) hc
  let E : fibreModel n b ≅ V :=
    hW.isoPullback ≪≫ endpointRelativeFibreIso d n (f ≫ j) π b c t hg' hc' ≪≫
      (hV.flip.paste_horiz hI).flip.isoPullback.symm
  exact appendModel_iso_connected E hVG

/-- A geometrically connected model has connected field fibres. -/
theorem appendModel_field_connected {R : Type u} [CommRing R] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of R)) [GeometricallyConnected a]
    (L : Type u) [Field L] (ρ : R →+* L) :
    ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ)) a : Scheme.{u}) := by
  let : GeometricallyConnected (pullback.fst (Spec.map (CommRingCat.ofHom ρ)) a) :=
    inferInstance
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.fst (Spec.map (CommRingCat.ofHom ρ)) a)

/-- The fibre of a scalar-extended map is the scalar extension of its fibre. -/
def pointScalarIso {B T : Scheme.{u}} (κ : T ⟶ B)
    {N F : Over B} (n : N ⟶ F) (b : Over.mk (𝟙 B) ⟶ F) :
    (scalarFunctor κ).obj (fibreModel n b) ≅
      fibreModel (chosenScalarArrow κ n) (scalarPoint κ b) :=
  Over.isoMk (scalarFibre_cartesian κ n b).isoPullback
    (scalarFibre_cartesian κ n b).isoPullback_hom_snd

/-- A specified equality replaces the lower leg of a Cartesian curve square. -/
theorem appendModel_curve_base {C F Q B : Scheme.{u}}
    {c : C ⟶ F} {t : C ⟶ B} {π : F ⟶ Q} {b b' : B ⟶ Q}
    (h : IsPullback c t π b) (hb : b' = b) : IsPullback c t π b' := by
  subst b'
  exact h

/-- A specified equality replaces the composite leg of an append square. -/
theorem appendModel_factor_square {N A F Q : Scheme.{u}}
    {d : N ⟶ A} {n : N ⟶ F} {a a' : A ⟶ F} {π : F ⟶ Q}
    (h : IsPullback d n (a ≫ π) π) (ha : a = a') :
    IsPullback d n (a' ≫ π) π := by
  subst a'
  exact h

private theorem original_fibre_base {B : Scheme.{u}} {N F : Over B}
    (n : N ⟶ F) (b : Over.mk (𝟙 B) ⟶ F) :
    pullback.fst n.left b.left ≫ N.hom = pullback.snd n.left b.left :=
  (fibreProjection n b).w

private theorem replace_bases {X Y T B : Scheme.{u}} {q : X ⟶ Y}
    {a a' : X ⟶ T} {b b' : Y ⟶ B} {κ : T ⟶ B}
    (h : IsPullback q a b κ) (ha : a = a') (hb : b = b') :
    IsPullback q a' b' κ := by
  subst a'
  subst b'
  exact h

/-- The coefficient model of a point retains its original comparison. -/
theorem appendModel_point_comparison {B T : Scheme.{u}} (κ : T ⟶ B)
    {NK FK : Over T} {N F : Over B} (nK : NK ⟶ FK) (n : N ⟶ F)
    (p : Over.mk (𝟙 T) ⟶ FK) (b : Over.mk (𝟙 B) ⟶ F)
    (qN : NK.left ⟶ N.left) (qF : FK.left ⟶ F.left)
    (hN : IsPullback qN NK.hom N.hom κ) (hF : IsPullback qF FK.hom F.hom κ)
    (hn : nK.left ≫ qF = qN ≫ n.left) (hp : p.left ≫ qF = κ ≫ b.left) :
    ∃ q : (fibreModel nK p).left ⟶ (fibreModel n b).left,
      IsPullback q (fibreModel nK p).hom (fibreModel n b).hom κ ∧
      q ≫ (fibreProjection n b).left = (fibreProjection nK p).left ≫ qN ∧
      q ≫ (fibreModel n b).hom = (fibreModel nK p).hom ≫ κ := by
  have hpoint : IsPullback κ (𝟙 T) (𝟙 B) κ :=
    IsPullback.of_vert_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
  have h := paired_model_scalar_pullback κ NK.hom (𝟙 T) FK.hom N.hom (𝟙 B) F.hom
    nK.left p.left n.left b.left nK.w p.w n.w b.w qN κ qF hN hpoint hF hn hp
  exact ⟨_, replace_bases h.1 (original_fibre_base nK p) (original_fibre_base n b),
    h.2.1, h.2.2⟩

end SchubertGeometry
