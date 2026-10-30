import Batteries.Tactic.OpenPrivate
import OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage

set_option autoImplicit false

/-! # Retaining finite families of specified comparison isomorphisms

The morphisms are fixed before their generic inverses are descended.
An equation at one common stage identifies those inverses with the
scalar extensions of the specified morphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting

namespace SchubertGeometry

universe u v

open private scalar_comparison cone_original extend_scalar_arrow iso_from_arrow_eq
  from OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage

private theorem iso_exists {B : Scheme.{u}} {X Y : Over B}
    (f : X ⟶ Y) (h : IsIso f.left) : ∃ E : X ≅ Y, E.hom = f := by
  let : IsIso f.left := h
  refine ⟨Over.isoMk (asIso f.left) f.w, ?_⟩
  apply (Over.forget B).map_injective
  rfl

private theorem scalar_cone_natural {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Over (Spec (.of S))} (f : X ⟶ Y)
    (i : CoefficientStage S) :
    (modelScalarCone S X.hom).π.app (op i) ≫
        (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f).left =
      (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) f).left ≫
        (modelScalarCone S Y.hom).π.app (op i) := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap i.val K))
  let κK := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let g := chosenScalarArrow κK f
  exact scalar_comparison κ ρ f g (pullback.snd κK X.hom) (pullback.snd κK Y.hom)
    ((modelScalarCone S X.hom).π.app (op i))
    ((modelScalarCone S Y.hom).π.app (op i))
    (modelScalarCone_cartesian S X.hom i) (modelScalarCone_cartesian S Y.hom i)
    (cone_original S X i) (cone_original S Y i) (chosenScalarArrow_snd κK f).symm

/-- A finite family of specified morphisms which are generically invertible
becomes invertible after one coefficient extension above the given stage.
The resulting morphisms are the scalar extensions of the original maps. -/
theorem exists_comparison_iso_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (X Y : I → Over (Spec (.of S)))
    [∀ i, CompactSpace (X i).left] [∀ i, QuasiSeparatedSpace (X i).left]
    [∀ i, CompactSpace (Y i).left] [∀ i, QuasiSeparatedSpace (Y i).left]
    [∀ i, LocallyOfFinitePresentation (X i).hom]
    [∀ i, LocallyOfFinitePresentation (Y i).hom]
    (f : ∀ i, X i ⟶ Y i)
    (hgeneric : ∀ i, IsIso
      (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (f i)).left)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k), ∀ i, IsIso
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (f i)).left := by
  let κK := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let E (i : I) := Classical.choose (iso_exists (chosenScalarArrow κK (f i)) (hgeneric i))
  have hE (i : I) : (E i).hom.left = (chosenScalarArrow κK (f i)).left :=
    congrArg Over.Hom.left
      (Classical.choose_spec (iso_exists (chosenScalarArrow κK (f i)) (hgeneric i)))
  obtain ⟨j, hstart, Ej, hEj, _⟩ := exists_retained_isos S hS
    (fun i => (X i).left) (fun i => (Y i).left)
    (fun i => (X i).hom) (fun i => (Y i).hom) E start
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let fj (i : I) : stageScalarModel S (X i).hom j ⟶ stageScalarModel S (Y i).hom j :=
    chosenScalarArrow κj (f i)
  have hmaps (i : I) : (modelScalarCone S (X i).hom).π.app (op j) ≫ (fj i).left =
      (modelScalarCone S (X i).hom).π.app (op j) ≫ (Ej i).hom.left :=
    (scalar_cone_natural S (f i) j).trans
      ((congrArg (fun a : (genericScalarModel S (X i).hom).left ⟶
          (genericScalarModel S (Y i).hom).left =>
        a ≫ (modelScalarCone S (Y i).hom).π.app (op j)) (hE i).symm).trans (hEj i).symm)
  obtain ⟨k, hjk, heq⟩ := exists_stage_arrow_eqs S hS
    (fun i => (X i).left) (fun i => (Y i).left)
    (fun i => (X i).hom) (fun i => (Y i).hom) j fj (fun i => (Ej i).hom) hmaps
  refine ⟨k, hstart.trans hjk, fun i => ?_⟩
  let Ek := retainedIsoExtend S (X i).hom (Y i).hom hjk (Ej i)
  exact iso_from_arrow_eq Ek _ ((extend_scalar_arrow S (f i) hjk).symm.trans (heq i))

end SchubertGeometry
