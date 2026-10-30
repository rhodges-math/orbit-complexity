import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.ContractionRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# specified generic maps from arithmetic cell models

The tensor comparison and the original affine counit identify each arithmetic
cell model's K-fibre with the same original cell intersection. Its original
Richardson projection is then carried into the generic fibre of a specified
Cartesian Richardson model. No equality between the models is assumed.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace SchubertGeometry.CellContraction

universe u

section GenericComparison

variable {R K A C : Type u} [CommRing R] [CommRing K] [CommRing A] [CommRing C]
    [Algebra R K] [Algebra R A] [Algebra K C]

/-- The specified tensor-spectrum comparison is an isomorphism over Spec K. -/
def tensorModelOverIso (e : K ⊗[R] A ≃ₐ[K] C) :
    Over.mk (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ≅
        (Spec (.of C)).asOver (Spec (.of K)) := by
  let p : Over.mk (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ≅
        (Spec (.of (K ⊗[R] A))).asOver (Spec (.of K)) :=
    Over.isoMk (pullbackSpecIso R K A) (by
      change (pullbackSpecIso R K A).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))) =
          pullback.fst _ _
      exact pullbackSpecIso_hom_fst' R K A)
  exact p ≪≫ (algSpec (.of K)).mapIso (CommAlgCat.isoMk e).symm.op

/-- The inverse tensor comparison retains the specified original coordinate
inclusion, with its ring equation checked before applying Spec. -/
theorem tensorModelOverIso_inv_snd
    [Algebra R C]
    (e : K ⊗[R] A ≃ₐ[K] C) (j : A →ₐ[R] C)
    (h : ∀ a : A, e ((1 : K) ⊗ₜ[R] a) = j a) :
    (tensorModelOverIso e).inv.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
      Spec.map (CommRingCat.ofHom j.toRingHom) := by
  have hRing : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom =
        j.toRingHom := by
    apply RingHom.ext
    intro a
    exact h a
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (pullbackSpecIso R K A).inv) ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom j.toRingHom)
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom (e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom)) = _
  exact congrArg (fun f : A →+* C => Spec.map (CommRingCat.ofHom f)) hRing

end GenericComparison

section ChosenModel

variable {K : Type u} [CommRing K] (R : Subalgebra ℤ K)

/-- A specified Cartesian model gives its specified generic-fibre isomorphism
over K, with no change to its source scheme or original model map. -/
def chosenGenericIso (Y : Over (Spec (.of K))) {D : Scheme.{u}}
    (d : D ⟶ Spec (.of R)) (q : Y.left ⟶ D)
    (h : IsPullback q Y.hom d
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    Y ≅ FrobeniusSplitting.genericScalarModel R d :=
  Over.isoMk h.flip.isoPullback (h.flip.isoPullback_hom_fst)

/-- The chosen generic isomorphism retains exactly the given model projection. -/
theorem chosenGenericIso_snd (Y : Over (Spec (.of K))) {D : Scheme.{u}}
    (d : D ⟶ Spec (.of R)) (q : Y.left ⟶ D)
    (h : IsPullback q Y.hom d
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    (chosenGenericIso R Y d q h).hom.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) d = q :=
  h.flip.isoPullback_hom_snd

end ChosenModel

private theorem over_trans_inv_snd
    {T : Type*} [Category T] {S : T} {A B C : Over S} {Z : T}
    (e : A ≅ B) (d : B ≅ C) {E : A ≅ C} (hE : E = e ≪≫ d)
    (p : A.left ⟶ Z) (q : B.left ⟶ Z) (he : e.inv.left ≫ p = q) :
    E.inv.left ≫ p = d.inv.left ≫ q := by
  subst E
  simp only [Iso.trans_inv, Over.comp_left, Category.assoc, he]

private theorem conjugated_map_comp
    {T : Type*} [Category T] {A B X Y : T}
    (e : A ≅ X) (d : Y ≅ B) (f : X ⟶ Y) {m : A ⟶ B}
    (hm : m = e.hom ≫ f ≫ d.hom) : m ≫ d.inv = e.hom ≫ f := by
  rw [hm]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem over_conjugated_left
    {T : Type*} [Category T] {S : T} {A B X Y : Over S}
    (e : A ≅ X) (d : Y ≅ B) (f : X ⟶ Y) {m : A ⟶ B}
    (hm : m = e.hom ≫ f ≫ d.hom) :
    m.left = e.hom.left ≫ f.left ≫ d.hom.left := by
  simp only [hm, Over.comp_left]

private theorem conjugated_map_projection
    {T : Type*} [Category T] {S : T} {A B X Y : Over S} {Z : T}
    (e : A ≅ X) (d : Y ≅ B) (f : X ⟶ Y) {m : A ⟶ B}
    (hm : m = e.hom ≫ f ≫ d.hom) (p : B.left ⟶ Z) (q : Y.left ⟶ Z)
    (hp : d.hom.left ≫ p = q) : m.left ≫ p = e.hom.left ≫ f.left ≫ q := by
  rw [over_conjugated_left e d f hm]
  rw [Category.assoc, Category.assoc, hp]

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)
    {R : Subalgebra ℤ K}

/-- The structure morphism of the specified affine arithmetic cell image model. -/
def cellArithmeticBase (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne)) :
    Spec (.of M.model) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R M.model))

/-- The original tensor comparison followed by the original affine counit
identifies this arithmetic cell fibre with the same original cell pullback. -/
def cellArithmeticGenericIso (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne)) :
    FrobeniusSplitting.genericScalarModel R (cellArithmeticBase G a b w hne M) ≅
      cellIntersection G a b w :=
  tensorModelOverIso M.comparison ≪≫ coefficientIso (cellIntersection G a b w)

/-- The generic arithmetic cell map is the original Richardson projection,
carried through the specified source and specified target comparison isomorphisms. -/
def cellArithmeticMap (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    {D : Scheme.{u}} (d : D ⟶ Spec (.of R))
    (qD : (richardsonVariety G a b).scheme ⟶ D)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec d
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    FrobeniusSplitting.genericScalarModel R (cellArithmeticBase G a b w hne M) ⟶
      FrobeniusSplitting.genericScalarModel R d :=
  (cellArithmeticGenericIso G a b w hne M).hom ≫
    pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b) ≫
    (chosenGenericIso R (richardsonVariety G a b).toOver d qD hD).hom

end SchubertGeometry.CellContraction
