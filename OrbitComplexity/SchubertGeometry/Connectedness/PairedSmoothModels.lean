import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Normality.Models.PairedGlobalModel
import OrbitComplexity.SchubertGeometry.Normality.Models.PairedAffineSmooth
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedProductSmooth

/-! # Initial smooth arithmetic models of the paired source

Affine intersections of the paired source are smooth by the pointed Borel
product. Their coordinate diagram therefore descends with smooth, hence flat,
nodes. The global source construction gives an arithmetic source model.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private intersectionCoordinates_finite from
  OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

private theorem coordinate_cocone_open {K I : Type u} [CommRing K]
    (X : Over (Spec (.of K)))
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (U : I → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
    IsOpenImmersion ((intersectionCoordinateCocone X.hom U hU).ι.app s).left := by
  let E := intersectionOpens U ⋙ X.left.restrictFunctor ⋙ Over.map X.hom
  let (t : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj t).left :=
    intersectionOpens_affine U hU t
  let iso := (Over.forget (Spec (.of K))).mapIso
    ((coordinateDiagramIso (.of K) E).app s)
  let V := (intersectionOpens U).obj s
  let inc : (E.obj s).left ⟶ X.left := V.ι
  let : IsIso iso.inv := Iso.isIso_inv iso
  let : IsOpenImmersion iso.inv := inferInstance
  let : IsOpenImmersion inc := by
    change IsOpenImmersion V.ι
    infer_instance
  change IsOpenImmersion (iso.inv ≫ inc)
  exact IsOpenImmersion.comp iso.inv inc

private theorem paired_coordinates_smooth
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    (A : Type u) [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A]
    (j : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶
      pairedBSDHSource G a b) [IsOpenImmersion j.left] : Algebra.Smooth K A := by
  let B := G.borelAlgebra ⊗[K] G.oppositeBorelAlgebra
  let : Algebra.Smooth K (A ⊗[K] B) := pairedBSDH_tensor_smooth G a b A j
  exact smooth_of_pointed_product K A B (Bialgebra.counitAlgHom K B)

/-- A finite affine cover of the paired source constructs an initial smooth
arithmetic model, with its Cartesian comparison to the source. -/
theorem exists_paired_smooth_model
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    [IsAffineHom (pullback.diagonal (terminal.from (pairedBSDHSource G a b).left))]
    [LocallyOfFinitePresentation (pairedBSDHSource G a b).hom]
    {I : Type u} [Finite I] (U : I → (pairedBSDHSource G a b).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤) :
    ∃ (R : Subalgebra ℤ K) (C : Over (Spec (.of R)))
      (q : (pairedBSDHSource G a b).left ⟶ C.left),
      R.FG ∧ CompactSpace C.left ∧ Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
      IsPullback q (pairedBSDHSource G a b).hom C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let X := pairedBSDHSource G a b
  let F := intersectionCoordinates X.hom (intersectionOpens U)
  let (s : {s : Finset I // s.Nonempty}) : Algebra.FinitePresentation K (F.obj s) :=
    intersectionCoordinates_finite X.hom U hU s
  have hsmooth (s : {s : Finset I // s.Nonempty}) : Algebra.Smooth K (F.obj s) := by
    let j : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s)))) ⟶ X :=
      (intersectionCoordinateCocone X.hom U hU).ι.app (op s)
    let : IsOpenImmersion j.left := coordinate_cocone_open X U hU (op s)
    exact paired_coordinates_smooth G a b (F.obj s) j
  obtain ⟨S, P, e, hS, hfp, hsm, hnat⟩ :=
    @exists_arithmetic_functor_smooth_on.{u,u,u}
      {s : Finset I // s.Nonempty} inferInstance inferInstance (fun _ _ => inferInstance)
      K (inferInstanceAs (CommRing K)) F (fun s => inferInstance)
      Set.univ (fun s _ => hsmooth s)
  let (s : {s : Finset I // s.Nonempty}) : Algebra.FinitePresentation S (P.obj s) := hfp s
  let (s : {s : Finset I // s.Nonempty}) : Algebra.Smooth S (P.obj s) := hsm s (Set.mem_univ s)
  obtain ⟨R, _hSR, C, q, hfg, hcompact, hs, hfinite, hq⟩ :=
    @pairedBSDH_global_source_model.{u} K
      (inferInstanceAs (Field K)) (inferInstanceAs (IsAlgClosed K))
      (inferInstanceAs (CharZero K)) G a b I inferInstance inferInstance
      U hU hcover S hS P (fun s => inferInstance) (fun s => inferInstance) e hnat
  exact ⟨R, C, q, hfg, hcompact, hs, hfinite, hq⟩

end SchubertGeometry
