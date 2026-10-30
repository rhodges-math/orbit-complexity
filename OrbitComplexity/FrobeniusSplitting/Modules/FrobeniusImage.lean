import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Sheaves.Sheaf

/-! # The image ring sheaf of absolute Frobenius -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting

private def powerOnOpen (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) :
    Γ(X, U) →+* Γ(X, U) :=
  ((sheafFrobenius C p base).hom.app (.op U)).hom

private theorem powerOnOpen_injective (C : Type u) [CommRing C] (p : ℕ)
    [ExpChar C p] {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (base : X ⟶ Spec (.of C)) (U : X.Opens) :
    Function.Injective (powerOnOpen C p base U) := by
  intro a b h
  apply sub_eq_zero.mp
  apply IsReduced.eq_zero (a - b)
  refine ⟨p, ?_⟩
  change powerOnOpen C p base U (a - b) = 0
  rw [map_sub, h, sub_self]

private def imageRing (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) : Subring Γ(X, U) :=
  (powerOnOpen C p base U).range

private def imageMap (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    imageRing C p base U.unop →+* imageRing C p base V.unop :=
  (((X.presheaf.map i).hom).comp (imageRing C p base U.unop).subtype).codRestrict
    (imageRing C p base V.unop) (by
      intro a
      obtain ⟨r, hr⟩ := a.property
      refine ⟨(X.presheaf.map i) r, ?_⟩
      change ((X.presheaf.map i) r) ^ p = (X.presheaf.map i) a.val
      change r ^ p = a.val at hr
      rw [← map_pow, hr])

private def imagePresheaf (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) : X.Opensᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (imageRing C p base U.unop)
  map i := RingCat.ofHom (imageMap C p base i)
  map_id U := by
    ext a
    change (X.presheaf.map (𝟙 U)) a.val = a.val
    simp
  map_comp i j := by
    ext a
    change (X.presheaf.map (i ≫ j)) a.val =
      (X.presheaf.map j) ((X.presheaf.map i) a.val)
    simp

private def powerRangeEquiv (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (base : X ⟶ Spec (.of C)) (U : X.Opens) : Γ(X, U) ≃+* imageRing C p base U :=
  RingEquiv.ofBijective (powerOnOpen C p base U).rangeRestrict
    ⟨fun _ _ h => powerOnOpen_injective C p base U (congrArg Subtype.val h),
      (powerOnOpen C p base U).rangeRestrict_surjective⟩

private def imagePresheafIso (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] (base : X ⟶ Spec (.of C)) :
    X.ringCatSheaf.obj ≅ imagePresheaf C p base :=
  NatIso.ofComponents (fun U => (powerRangeEquiv C p base U.unop).toRingCatIso) (by
    intro U V i
    ext r
    apply Subtype.ext
    change ((X.presheaf.map i) r) ^ p = (X.presheaf.map i) (r ^ p)
    exact ((X.presheaf.map i).hom.map_pow r p).symm)

/-- The ring sheaf whose sections are the pth powers in the structure sheaf. -/
def frobeniusImageSheaf (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] (base : X ⟶ Spec (.of C)) :
    Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u} :=
  ⟨imagePresheaf C p base,
    (Presheaf.isSheaf_of_iso_iff (imagePresheafIso C p base)).mp X.ringCatSheaf.property⟩

/-- Frobenius identifies the structure sheaf with its image ring sheaf. -/
def frobeniusImageIso (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] (base : X ⟶ Spec (.of C)) :
    X.ringCatSheaf ≅ frobeniusImageSheaf C p base :=
  ObjectProperty.isoMk _ (imagePresheafIso C p base)

/-- The image ring sheaf is included by the inclusion of pth-power subrings. -/
def frobeniusImageInclusion (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] (base : X ⟶ Spec (.of C)) :
    frobeniusImageSheaf C p base ⟶ X.ringCatSheaf where
  hom.app U := RingCat.ofHom (imageRing C p base U.unop).subtype
  hom.naturality {U V} i := by
    ext a
    rfl

/-- This image factorization is the absolute-Frobenius map, including its
action on coefficients. -/
theorem frobeniusImageIso_factor (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] (base : X ⟶ Spec (.of C)) :
    (frobeniusImageIso C p base).hom ≫ frobeniusImageInclusion C p base =
      sheafFrobenius C p base := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext r
  rfl

end FrobeniusSplitting
