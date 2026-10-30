import Batteries.Tactic.OpenPrivate
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixSquareRetention
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateSquares
import OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
import Mathlib.AlgebraicGeometry.Noetherian

set_option autoImplicit false

/-! # Cartesian squares over a common coefficient stage

The comparison into each specified pullback is formed before scalar
extension. Its generic inverse is retained, so the squares at the final
stage use the original morphisms and both original projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting

namespace SchubertGeometry

universe u v

open private scalar_functor scalar_preserves_limit
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected

private theorem comparison_iso {T : Type*} [Category T] [HasPullbacks T]
    {A B C D P : T} {f : A ⟶ B} {g : A ⟶ C} {p : B ⟶ D} {q : C ⟶ D}
    {r : P ⟶ B} {s : P ⟶ C} (h : IsPullback f g p q) (hP : IsPullback r s p q)
    (c : A ⟶ P) (hr : c ≫ r = f) (hs : c ≫ s = g) : IsIso c := by
  let E := h.isoPullback ≪≫ hP.isoPullback.symm
  have heq : c = E.hom := by
    apply hP.hom_ext
    · exact hr.trans (by
        simp only [E, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          hP.isoPullback_inv_fst, h.isoPullback_hom_fst])
    · exact hs.trans (by
        simp only [E, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          hP.isoPullback_inv_snd, h.isoPullback_hom_snd])
  rw [heq]
  infer_instance

private theorem cartesian_of_comparison {T : Type*} [Category T] [HasPullbacks T]
    {A B C D P : T} {f : A ⟶ B} {g : A ⟶ C} {p : B ⟶ D} {q : C ⟶ D}
    {r : P ⟶ B} {s : P ⟶ C} (hP : IsPullback r s p q)
    (c : A ⟶ P) [IsIso c] (hr : c ≫ r = f) (hs : c ≫ s = g)
    (hw : f ≫ p = g ≫ q) : IsPullback f g p q := by
  refine IsPullback.of_iso_pullback ⟨hw⟩ (asIso c ≪≫ hP.isoPullback) ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => c ≫ k) hP.isoPullback_hom_fst).trans hr)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => c ≫ k) hP.isoPullback_hom_snd).trans hs)

private def square_target {B : Scheme.{u}} {Y Z W : Over B}
    (p : Y ⟶ W) (q : Z ⟶ W) : Over B :=
  Over.mk (pullback.fst p.left q.left ≫ Y.hom)

private def square_fst {B : Scheme.{u}} {Y Z W : Over B}
    (p : Y ⟶ W) (q : Z ⟶ W) : square_target p q ⟶ Y :=
  Over.homMk (pullback.fst p.left q.left) rfl

private def square_snd {B : Scheme.{u}} {Y Z W : Over B}
    (p : Y ⟶ W) (q : Z ⟶ W) : square_target p q ⟶ Z :=
  Over.homMk (pullback.snd p.left q.left) (by
    calc
      pullback.snd p.left q.left ≫ Z.hom =
          pullback.snd p.left q.left ≫ (q.left ≫ W.hom) :=
        congrArg (fun k => pullback.snd p.left q.left ≫ k) q.w.symm
      _ = (pullback.snd p.left q.left ≫ q.left) ≫ W.hom :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst p.left q.left ≫ p.left) ≫ W.hom :=
        congrArg (fun k => k ≫ W.hom) (pullback.condition (f := p.left) (g := q.left)).symm
      _ = pullback.fst p.left q.left ≫ Y.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => pullback.fst p.left q.left ≫ k) p.w))

private theorem square_cartesian {B : Scheme.{u}} {Y Z W : Over B}
    (p : Y ⟶ W) (q : Z ⟶ W) :
    IsPullback (square_fst p q) (square_snd p q) p q := by
  apply IsPullback.of_map_of_faithful (Over.forget B)
  exact IsPullback.of_hasPullback p.left q.left

private def square_comparison {B : Scheme.{u}} {X Y Z W : Over B}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (hw : f ≫ p = g ≫ q) : X ⟶ square_target p q :=
  Over.homMk
    (pullback.lift f.left g.left (congrArg (fun k => k.left) hw)) (by
      change pullback.lift _ _ _ ≫ (pullback.fst p.left q.left ≫ Y.hom) = X.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact f.w)

private theorem comparison_fst {B : Scheme.{u}} {X Y Z W : Over B}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (hw : f ≫ p = g ≫ q) : square_comparison f g p q hw ≫ square_fst p q = f := by
  apply (Over.forget B).map_injective
  exact pullback.lift_fst _ _ _

private theorem comparison_snd {B : Scheme.{u}} {X Y Z W : Over B}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (hw : f ≫ p = g ≫ q) : square_comparison f g p q hw ≫ square_snd p q = g := by
  apply (Over.forget B).map_injective
  exact pullback.lift_snd _ _ _

private theorem square_properties {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Y Z W : Over (Spec (.of R))} [IsAffine Y.left] [IsAffine Z.left] [IsAffine W.left]
    [LocallyOfFinitePresentation Y.hom] [LocallyOfFinitePresentation Z.hom]
    [LocallyOfFinitePresentation W.hom] (p : Y ⟶ W) (q : Z ⟶ W) :
    LocallyOfFinitePresentation (square_target p q).hom ∧
      CompactSpace (square_target p q).left ∧
      QuasiSeparatedSpace (square_target p q).left := by
  let : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  let : LocallyOfFiniteType (q.left ≫ W.hom) := q.w.symm ▸
    (inferInstanceAs (LocallyOfFiniteType Z.hom))
  let : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left W.hom
  let : LocallyOfFinitePresentation q.left := inferInstance
  let : LocallyOfFinitePresentation (square_target p q).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst p.left q.left ≫ Y.hom))
  let : IsAffine (square_target p q).left :=
    inferInstanceAs (IsAffine (pullback p.left q.left))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem comparison_generic_iso {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y Z W : Over B} (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (hw : f ≫ p = g ≫ q)
    (hgeneric : IsPullback (chosenScalarArrow κ f).left (chosenScalarArrow κ g).left
      (chosenScalarArrow κ p).left (chosenScalarArrow κ q).left) :
    IsIso (chosenScalarArrow κ (square_comparison f g p q hw)).left := by
  let F := scalar_functor κ
  have h : IsPullback (F.map f) (F.map g) (F.map p) (F.map q) :=
    IsPullback.of_map_of_faithful (Over.forget T) hgeneric
  have hP := (square_cartesian p q).map F
  let c := F.map (square_comparison f g p q hw)
  let : IsIso c := comparison_iso h hP c
    ((F.map_comp _ _).symm.trans (congrArg F.map (comparison_fst f g p q hw)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (comparison_snd f g p q hw)))
  exact inferInstanceAs (IsIso ((Over.forget T).map c))

private theorem scalar_square {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y Z W : Over B} (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ W) (q : Z ⟶ W)
    (hw : f ≫ p = g ≫ q)
    (hc : IsIso (chosenScalarArrow κ (square_comparison f g p q hw)).left) :
    IsPullback (chosenScalarArrow κ f).left (chosenScalarArrow κ g).left
      (chosenScalarArrow κ p).left (chosenScalarArrow κ q).left := by
  let F := scalar_functor κ
  let c := F.map (square_comparison f g p q hw)
  let : IsIso ((Over.forget T).map c) := hc
  let : IsIso c := isIso_of_reflects_iso c (Over.forget T)
  have hP := (square_cartesian p q).map F
  have h := cartesian_of_comparison hP c
    ((F.map_comp _ _).symm.trans (congrArg F.map (comparison_fst f g p q hw)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (comparison_snd f g p q hw)))
    ((F.map_comp _ _).symm.trans
      ((congrArg F.map hw).trans (F.map_comp _ _)))
  exact h.map (Over.forget T)

/-- Finitely many Cartesian generic squares of affine coefficient models
remain Cartesian at a common stage using the original four maps. -/
theorem exists_prefix_square_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (X Y Z W : I → Over (Spec (.of S)))
    [∀ i, IsAffine (X i).left] [∀ i, IsAffine (Y i).left]
    [∀ i, IsAffine (Z i).left] [∀ i, IsAffine (W i).left]
    [∀ i, LocallyOfFinitePresentation (X i).hom]
    [∀ i, LocallyOfFinitePresentation (Y i).hom]
    [∀ i, LocallyOfFinitePresentation (Z i).hom]
    [∀ i, LocallyOfFinitePresentation (W i).hom]
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, X i ⟶ Z i)
    (p : ∀ i, Y i ⟶ W i) (q : ∀ i, Z i ⟶ W i)
    (hw : ∀ i, f i ≫ p i = g i ≫ q i)
    (hgeneric : ∀ i, IsPullback
      (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (f i)).left
      (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (g i)).left
      (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (p i)).left
      (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (q i)).left)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k), ∀ i,
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      IsPullback (chosenScalarArrow κ (f i)).left (chosenScalarArrow κ (g i)).left
        (chosenScalarArrow κ (p i)).left (chosenScalarArrow κ (q i)).left := by
  let : IsNoetherianRing S := isNoetherianRing_of_fg hS
  let P (i : I) := square_target (p i) (q i)
  have hP (i : I) := square_properties (p i) (q i)
  let (i : I) : LocallyOfFinitePresentation (P i).hom := (hP i).1
  let (i : I) : CompactSpace (P i).left := (hP i).2.1
  let (i : I) : QuasiSeparatedSpace (P i).left := (hP i).2.2
  let c (i : I) : X i ⟶ P i := square_comparison (f i) (g i) (p i) (q i) (hw i)
  obtain ⟨k, hstart, hc⟩ := exists_comparison_iso_stage S hS X P c
    (fun i => comparison_generic_iso _ (f i) (g i) (p i) (q i) (hw i) (hgeneric i)) start
  exact ⟨k, hstart, fun i => scalar_square _ (f i) (g i) (p i) (q i) (hw i) (hc i)⟩

end SchubertGeometry
