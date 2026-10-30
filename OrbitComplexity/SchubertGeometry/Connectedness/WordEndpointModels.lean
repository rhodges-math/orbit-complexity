import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ProperAppend
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.CoefficientLimit
import Mathlib.Data.Finset.Lattice.Fold
import Batteries.Tactic.Lint

/-! # Finite families of Bott–Samelson source models

Every prescribed finite family of words has proper, smooth, geometrically
connected arithmetic source models over one coefficient stage. Each comparison
retains both projections of the scalar square. The endpoint arrows and their
connected fibres are separate from connectedness of these sources over the
coefficient base.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry

universe u v

private theorem finite_coefficient_upper
    {K : Type u} [CommRing K] {I : Type v} [Finite I]
    (S : Subalgebra ℤ K) (hS : S.FG) (R : I → Subalgebra ℤ K)
    (hR : ∀ i, (R i).FG) :
    ∃ T : Subalgebra ℤ K, S ≤ T ∧ T.FG ∧ ∀ i, R i ≤ T := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hfin (s : Finset I) : (s.sup R).FG := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using (Subalgebra.fg_adjoin_finset (R := ℤ) (∅ : Finset K))
    | @insert i s _hi ih =>
        simpa only [Finset.sup_insert] using (hR i).sup ih
  refine ⟨S ⊔ Finset.univ.sup R, le_sup_left, hS.sup (hfin _), ?_⟩
  intro i
  exact (Finset.le_sup (Finset.mem_univ i)).trans le_sup_right

private theorem coefficient_triangle
    {K : Type u} [CommRing K] (R T : Subalgebra ℤ K) (hRT : R ≤ T) :
    Spec.map (CommRingCat.ofHom (algebraMap T K)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [← Spec.map_comp]
  congr 1

private theorem source_scalar_square
    {B BK T X Y : Scheme.{u}} (κ : T ⟶ B) (ρ : BK ⟶ T) (σ : BK ⟶ B)
    (a : X ⟶ BK) (b : Y ⟶ B) (q : X ⟶ Y)
    (hρ : ρ ≫ κ = σ) (h : IsPullback q a b σ) :
    ∃ qT : X ⟶ pullback κ b,
      qT ≫ pullback.fst κ b = a ≫ ρ ∧
      qT ≫ pullback.snd κ b = q ∧
      IsPullback qT a (pullback.fst κ b) ρ := by
  have hw : (a ≫ ρ) ≫ κ = q ≫ b := by
    rw [Category.assoc, hρ]
    exact h.w.symm
  let qT : X ⟶ pullback κ b := pullback.lift (a ≫ ρ) q hw
  have hfst : qT ≫ pullback.fst κ b = a ≫ ρ :=
    pullback.lift_fst _ _ _
  have hsnd : qT ≫ pullback.snd κ b = q :=
    pullback.lift_snd _ _ _
  have houter : IsPullback (qT ≫ pullback.snd κ b) a b (ρ ≫ κ) := by
    rw [hsnd, hρ]
    exact h
  refine ⟨qT, hfst, hsnd, ?_⟩
  exact houter.of_right hfst (IsPullback.of_hasPullback κ b).flip

private theorem source_scalar_properties
    {B T Y : Scheme.{u}} (κ : T ⟶ B) (b : Y ⟶ B)
    [IsProper b] [Smooth b] [GeometricallyConnected b] :
    IsProper (pullback.fst κ b) ∧ Smooth (pullback.fst κ b) ∧
      GeometricallyConnected (pullback.fst κ b) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A finite family of words has proper, smooth, geometrically connected source
models at one coefficient stage above any prescribed stage. The comparisons
with the characteristic-zero sources are Cartesian. -/
theorem exists_bsdh_family_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} [Finite I] (G : ReductiveGroupData K)
    (words : I → List G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (Y : I → Scheme.{u}) (base : ∀ i, Y i ⟶ Spec (.of k.val))
      (q : ∀ i, bsdhScheme G (words i) ⟶ Y i),
      ∀ i, IsProper (base i) ∧ Smooth (base i) ∧
        GeometricallyConnected (base i) ∧
        IsPullback (q i) (bsdhToSpec G (words i)) (base i)
          (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) := by
  classical
  choose R _hSR hR Y a q hp hs hg hcart using
    fun i => exists_proper_bsdh_model G (words i) S hS
  obtain ⟨T, hstart, hT, hRT⟩ :=
    finite_coefficient_upper start.val start.property.1 R hR
  let k : CoefficientStage S := ⟨T, hT, start.property.2.trans hstart⟩
  let κ (i : I) : Spec (.of T) ⟶ Spec (.of (R i)) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hRT i)).toRingHom)
  let ρ : Spec (.of K) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T K))
  choose qT _hfst _hsnd hcartT using fun i =>
    source_scalar_square (κ i) ρ
      (Spec.map (CommRingCat.ofHom (algebraMap (R i) K)))
      (bsdhToSpec G (words i)) (a i) (q i)
      (coefficient_triangle (R i) T (hRT i)) (hcart i)
  refine ⟨k, hstart, (fun i => pullback (κ i) (a i)),
    (fun i => pullback.fst (κ i) (a i)), qT, ?_⟩
  intro i
  let : IsProper (a i) := hp i
  let : Smooth (a i) := hs i
  let : GeometricallyConnected (a i) := hg i
  exact ⟨(source_scalar_properties (κ i) (a i)).1,
    (source_scalar_properties (κ i) (a i)).2.1,
    (source_scalar_properties (κ i) (a i)).2.2, hcartT i⟩

end SchubertGeometry
