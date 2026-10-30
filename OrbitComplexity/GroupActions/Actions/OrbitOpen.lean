import OrbitComplexity.GroupActions.Actions.OrbitSmooth
import OrbitComplexity.GroupActions.Actions.RightTranslations
import OrbitComplexity.GroupActions.Varieties.OpenPointLifts
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Open action families on homogeneous varieties

If a group acts transitively on a variety in characteristic zero, composing the action
with a morphism on the second factor is open. The second factor may be singular.
Smoothness of the orbit maps makes each rational slice open, and rational points detect
containment in the interior of the full scheme image.

## Main results

* `GroupActions.actionFamily_isOpen`: action families with a transitive target are open.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K]

private def fibreSlice (A B : Variety K) (b : B.points) :
    A.toOver ⟶ A.toOver ⊗ B.toOver :=
  lift (𝟙 A.toOver) (toUnit A.toOver ≫ B.pointsEquivOverHom b)

private theorem product_point_slice (A B : Variety K) [Smooth A.toSpec]
    (z : (Variety.smoothProductVariety A B).points) :
    ∃ a : A.points, ∃ b : B.points, Variety.mapPoints (fibreSlice A B b) a = z := by
  let P := Variety.smoothProductVariety A B
  let q := P.pointsEquivOverHom z
  let a := A.pointsEquivOverHom.symm (q ≫ fst A.toOver B.toOver)
  let b := B.pointsEquivOverHom.symm (q ≫ snd A.toOver B.toOver)
  refine ⟨a, b, ?_⟩
  apply P.pointsEquivOverHom.injective
  change A.pointsEquivOverHom a ≫ fibreSlice A B b = q
  have hunit : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) =
      𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
  have hq : q = lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [lift_fst, lift_snd, a, b, Equiv.apply_symm_apply]
  calc
    _ = lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) := by
      simp only [fibreSlice, comp_lift, Category.comp_id, comp_toUnit_assoc, hunit,
        Category.id_comp]
    _ = q := hq.symm


/-- Open rational slices make a morphism from a product open. -/
private theorem isOpenMap_of_slices [IsAlgClosed K] (A B C : Variety K) [Smooth A.toSpec]
    (f : (Variety.smoothProductVariety A B).toOver ⟶ C.toOver)
    (hf : ∀ b : B.points, IsOpenMap ((fibreSlice A B b) ≫ f).left) : IsOpenMap f.left := by
  let P := Variety.smoothProductVariety A B
  intro U hU
  let Uo : P.scheme.Opens := ⟨U, hU⟩
  let Q := P.openSubvariety Uo
  let fU : Q.toOver ⟶ C.toOver := P.openInclusion Uo ≫ f
  let V : C.scheme.Opens := ⟨interior (f.left '' U), isOpen_interior⟩
  have hrange : Set.range fU.left ⊆ (V : Set C.scheme) := by
    apply Variety.range_subset_open_of_points fU V
    intro p
    let z := Variety.mapPoints (P.openInclusion Uo) p
    obtain ⟨a, b, hab⟩ := product_point_slice A B z
    let s := fibreSlice A B b
    have hs : s.left (A.pointMap a) = P.pointMap z := congrArg P.pointMap hab
    have hz : P.pointMap z ∈ U := by
      change Uo.ι (Q.pointMap p) ∈ U
      exact (Q.pointMap p).property
    have hpre : A.pointMap a ∈ s.left ⁻¹' U := by
      change s.left (A.pointMap a) ∈ U
      rw [hs]
      exact hz
    have hopen : IsOpen ((s ≫ f).left '' (s.left ⁻¹' U)) :=
      hf b _ (hU.preimage s.left.continuous)
    have hsub : (s ≫ f).left '' (s.left ⁻¹' U) ⊆ f.left '' U := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨s.left v, hv, rfl⟩
    apply interior_maximal hsub hopen
    refine ⟨A.pointMap a, hpre, ?_⟩
    change f.left (s.left (A.pointMap a)) = C.pointMap (Variety.mapPoints fU p)
    rw [hs]
    rfl
  rw [← subset_interior_iff_isOpen]
  rintro _ ⟨z, hz, rfl⟩
  exact hrange ⟨(⟨z, hz⟩ : Uo), rfl⟩


variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
  [IrreducibleSpace H.scheme]

private theorem transitive_orbit_smooth (x : X.points)
    (hx : Surjective (Variety.orbitMorphism H X x).left) (y : X.points) :
    Smooth (Variety.orbitMorphism H X y).left := by
  let q := orbitProjection H X x
  let i := orbitInclusion H X x
  have hi : Surjective i.left := by
    constructor
    intro z
    obtain ⟨h, hh⟩ := hx.surj z
    refine ⟨q.left h, ?_⟩
    have hfac := congrArg Over.Hom.left (orbitProjection_fac H X x)
    exact (congrArg (fun f => f h) hfac).trans hh
  have hclosed : IsClosed (Set.range i.left) := by
    rw [Set.range_eq_univ.mpr hi.surj]
    exact isClosed_univ
  have : IsClosedImmersion i.left := .of_isPreimmersion _ hclosed
  have : IsReduced X.toOver.left := X.reduced
  have : IsIso i.left := isIso_of_isClosedImmersion_of_surjective i.left
  have : Smooth q.left := orbitProjection_smooth H X x
  have hqx : Smooth (Variety.orbitMorphism H X x).left := by
    have h : Smooth (q.left ≫ i.left) := inferInstance
    have hfac := congrArg Over.Hom.left (orbitProjection_fac H X x)
    exact hfac ▸ h
  obtain ⟨a, ha⟩ := Variety.exists_mapPoints_eq (Variety.orbitMorphism H X x) y
    (hx.surj (X.pointMap y))
  have hay : a • x = y := by
    rwa [Variety.mapPoints_orbitMorphism] at ha
  have he : (rightTranslation H a).hom ≫ Variety.orbitMorphism H X x =
      Variety.orbitMorphism H X y := by
    apply Variety.mapPoints_injective
    funext h
    rw [Variety.mapPoints_comp, rightTranslation_points,
      Variety.mapPoints_orbitMorphism, Variety.mapPoints_orbitMorphism, mul_smul, hay]
  have h : Smooth ((rightTranslation H a).hom.left ≫
      (Variety.orbitMorphism H X x).left) := inferInstance
  exact congrArg Over.Hom.left he ▸ h

/-- Action families on a transitive target are open, including for singular source varieties. -/
theorem actionFamily_isOpen (x : X.points)
    (hx : Surjective (Variety.orbitMorphism H X x).left) (Y : Variety K)
    (j : Y.toOver ⟶ X.toOver) :
    IsOpenMap ((H.toOver ◁ j) ≫ γ[H.toOver, X.toOver]).left := by
  have : Smooth H.toSpec :=
    TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced H.toSpec
  apply isOpenMap_of_slices H Y X ((H.toOver ◁ j) ≫ γ[H.toOver, X.toOver])
  intro y
  have : Smooth (Variety.orbitMorphism H X (Variety.mapPoints j y)).left :=
    transitive_orbit_smooth H X x hx _
  have hs : fibreSlice H Y y ≫ (H.toOver ◁ j) ≫ γ[H.toOver, X.toOver] =
      Variety.orbitMorphism H X (Variety.mapPoints j y) := by
    simp only [fibreSlice, lift_whiskerLeft_assoc, Variety.orbitMorphism]
    rfl
  have h : IsOpenMap (Variety.orbitMorphism H X (Variety.mapPoints j y)).left :=
    Scheme.Hom.isOpenMap _
  exact (congrArg Over.Hom.left hs).symm ▸ h

end

end GroupActions
