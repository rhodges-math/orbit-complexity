import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageAnchorMaps

/-!
# Cartesian comparisons with coefficient stages

The generic scalar cone is a Cartesian square over each coefficient stage.
An isomorphic generic model retains the same Cartesian comparison.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u

private theorem inner_square {T : Type*} [Category T]
    {P Q X B Bi K : T} {pg : P ⟶ K} {qg : P ⟶ X}
    {pi : Q ⟶ Bi} {qi : Q ⟶ X} {a : X ⟶ B}
    {κK : K ⟶ B} {κi : Bi ⟶ B} {κ : K ⟶ Bi}
    (hG : IsPullback qg pg a κK) (hI : IsPullback qi pi a κi) {f : P ⟶ Q}
    (hbase : f ≫ pi = pg ≫ κ) (horiginal : f ≫ qi = qg) (hκ : κ ≫ κi = κK) :
    IsPullback f pg pi κ := by
  apply IsPullback.of_right ?_ hbase hI
  simpa only [horiginal, hκ] using hG

private theorem coefficient_triangle {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (i : CoefficientStage S) :
    Spec.map (CommRingCat.ofHom (algebraMap i.val K)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
  have h : CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom ≫
        CommRingCat.ofHom (algebraMap i.val K) =
      CommRingCat.ofHom (algebraMap S K) := by
    ext x
    rfl
  exact (Spec.map_comp _ _).symm.trans
    (congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of K => Spec.map f) h)

private theorem model_scalar_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) a =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) a := by
  change pullback.lift _ _ _ ≫ pullback.snd _ a = _
  exact pullback.lift_snd _ _ _

/-- The generic scalar cone is Cartesian over every coefficient stage. -/
theorem modelScalarCone_cartesian {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    IsPullback ((modelScalarCone S a).π.app (op i))
      (genericScalarModel S a).hom (stageScalarModel S a i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap i.val K))) :=
  inner_square
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap S K))) a).flip
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) a).flip
    (modelScalarCone_base S a i) (model_scalar_original S a i) (coefficient_triangle S i)

private theorem iso_comp_square {T : Type*} [Category T] {B B' : T}
    {U V : Over B} {W : Over B'} (E : U ≅ V) (q : V.left ⟶ W.left) (κ : B ⟶ B')
    (h : IsPullback q V.hom W.hom κ) :
    IsPullback (E.hom.left ≫ q) U.hom W.hom κ := by
  have hE : IsPullback E.hom.left U.hom V.hom (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨E.hom.w.trans (Category.comp_id _).symm⟩
  simpa only [Category.id_comp] using hE.paste_horiz h

/-- A specified generic-model isomorphism gives the Cartesian comparison with
each scalar stage of that same model. -/
theorem overIso_modelStage_cartesian {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S)
    (Y : Over (Spec (.of K))) (E : Y ≅ genericScalarModel S a) :
    IsPullback (E.hom.left ≫ (modelScalarCone S a).π.app (op i))
      Y.hom (stageScalarModel S a i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap i.val K))) :=
  iso_comp_square (W := stageScalarModel S a i) E _ _ (modelScalarCone_cartesian S a i)

end FrobeniusSplitting
