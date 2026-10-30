import OrbitComplexity.SchubertGeometry.Connectedness.ProjectiveCurveRetention
import OrbitComplexity.SchubertGeometry.Connectedness.ElementaryCurves
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AffineChartAlgebra
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import OrbitComplexity.SchubertGeometry.ProjectiveLine.PolynomialChart
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false

/-! # Coordinates of the affine charts of a curve intersection

Pulling the two polynomial charts through a chosen projective-line
isomorphism gives affine charts of the same closed intersection. Their
global sections carry surjective polynomial coordinate maps, and their
spectrum comparisons retain both intersection projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open ReductiveGroups SchubertGeometry.CellContraction
open Polynomial

namespace SchubertGeometry

universe u

private theorem with_witness {A : Type*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private theorem make_witness {A : Type*} {B : A → Type*} {C : ∀ a, B a → Type*}
    {P : ∀ a b, C a b → Prop} (a : A) (b : B a) (c : C a b) (h : P a b c) :
    ∃ (a : A) (b : B a) (c : C a b), P a b c := ⟨a, b, c, h⟩

private theorem left_comp_eq {T : Type*} [Category T] {S : T}
    {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hh : f ≫ g = h) : f.left ≫ g.left = h.left :=
  congrArg (fun k : X ⟶ Z => k.left) hh

private def intersection_chart_map {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    pullback (o ≫ d) j ⟶ pullback d j :=
  pullback.lift (pullback.fst (o ≫ d) j ≫ o) (pullback.snd (o ≫ d) j)
    (by rw [Category.assoc]; exact pullback.condition)

private theorem intersection_chart_fst {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    intersection_chart_map d j o ≫ pullback.fst d j =
      pullback.fst (o ≫ d) j ≫ o :=
  pullback.lift_fst _ _ _

private theorem intersection_chart_snd {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    intersection_chart_map d j o ≫ pullback.snd d j = pullback.snd (o ≫ d) j :=
  pullback.lift_snd _ _ _

private theorem intersection_chart_square {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    IsPullback (intersection_chart_map d j o) (pullback.fst (o ≫ d) j)
      (pullback.fst d j) o := by
  have houter : IsPullback (intersection_chart_map d j o ≫ pullback.snd d j)
      (pullback.fst (o ≫ d) j) j (o ≫ d) := by
    rw [intersection_chart_snd]
    exact (IsPullback.of_hasPullback (o ≫ d) j).flip
  exact houter.of_right (intersection_chart_fst d j o)
    (IsPullback.of_hasPullback d j).flip

private theorem square_of_iso {T : Type*} [Category T]
    {P P' X Y Z : T} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) (E : P' ≅ P) (p' : P' ⟶ X) (q' : P' ⟶ Y)
    (hp : E.hom ≫ p = p') (hq : E.hom ≫ q = q') : IsPullback p' q' f g :=
  h.of_iso' E (Iso.refl X) (Iso.refl Y) (Iso.refl Z)
    (hp.trans (Category.comp_id _).symm) (hq.trans (Category.comp_id _).symm)
    (by simp) (by simp)

private instance chart_affine {R : Type u} [CommRing R]
    {C F Y : Scheme.{u}} (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j]
    (o : Spec (.of R[X]) ⟶ C) : IsAffine (pullback (o ≫ d) j : Scheme.{u}) :=
  isAffine_of_isAffineHom (pullback.fst (o ≫ d) j)

private theorem affine_chart_ring {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} [IsAffine Z] (f : Z ⟶ Spec (.of R[X])) [IsClosedImmersion f] :
    let X : Over (Spec (.of R)) := Over.mk
      (f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
    let _ : IsAffine X.left := inferInstanceAs (IsAffine Z)
    let _ : Algebra R Γ(Z, ⊤) := coefficientAlgebra X
    ∃ c : R[X] →ₐ[R] Γ(Z, ⊤), Function.Surjective c ∧
      Algebra.FinitePresentation R Γ(Z, ⊤) ∧
      Spec.map (CommRingCat.ofHom c.toRingHom) = Z.isoSpec.inv ≫ f := by
  intro X hX inst
  let : IsAffine X.left := hX
  let : Algebra R Γ(X.left, ⊤) := inst
  let a : X ⟶ (Spec (.of R[X])).asOver (Spec (.of R)) := Over.homMk f rfl
  let c := chartAlgHom X a
  have hc : Function.Surjective c := by
    change Function.Surjective (CommRingCat.ofHom c.toRingHom).hom
    rw [chartAlgHom_eq X a]
    exact closedChartCoordinates_surjective f
  let : Algebra.FiniteType R Γ(Z, ⊤) := Algebra.FiniteType.of_surjective c hc
  exact ⟨c, hc, Algebra.FinitePresentation.of_finiteType.mp inferInstance,
    chartAlgHom_square X a⟩

private theorem unique_coeff_map {S R σ : Type u} [CommRing S] [CommRing R]
    [Unique σ] (f : S →+* R) :
    (MvPolynomial.uniqueAlgEquiv R σ).toRingHom.comp (MvPolynomial.map f) =
      (Polynomial.mapRingHom f).comp (MvPolynomial.uniqueAlgEquiv S σ).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro z
    change MvPolynomial.eval₂ (Polynomial.C : R →+* R[X])
        (fun _ : σ => Polynomial.X) (MvPolynomial.map f (MvPolynomial.C z)) =
      Polynomial.map f (MvPolynomial.eval₂ (Polynomial.C : S →+* S[X])
        (fun _ : σ => Polynomial.X) (MvPolynomial.C z))
    simp only [MvPolynomial.map_C, MvPolynomial.eval₂_C, Polynomial.map_C]
  · intro z
    change MvPolynomial.eval₂ (Polynomial.C : R →+* R[X])
        (fun _ : σ => Polynomial.X) (MvPolynomial.map f (MvPolynomial.X z)) =
      Polynomial.map f (MvPolynomial.eval₂ (Polynomial.C : S →+* S[X])
        (fun _ : σ => Polynomial.X) (MvPolynomial.X z))
    simp only [MvPolynomial.map_X, MvPolynomial.eval₂_X, Polynomial.map_X]

private theorem spec_unique_coeff {S R σ : Type u} [CommRing S] [CommRing R]
    [Unique σ] (f : S →+* R) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R σ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv S σ).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h : CommRingCat.of (MvPolynomial σ S) ⟶ CommRingCat.of R[X] =>
    Spec.map h) (congrArg CommRingCat.ofHom (unique_coeff_map (σ := σ) f))

private theorem polynomial_chart_eq (R : Type u) [CommRing R]
    (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart R j =
      Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
          projectiveChartMap R (ULift.{u} (Fin 2)) j := rfl

/-- Both polynomial charts of a projective line commute with coefficient change. -/
theorem projectivePolynomialChart_coeff {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart R j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        projectiveLinePolynomialChart S j := by
  calc
    projectiveLinePolynomialChart R j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
        (Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
            {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
          projectiveChartMap R (ULift.{u} (Fin 2)) j) ≫
            projectiveCoeffMap (ULift.{u} (Fin 2)) f := by rw [polynomial_chart_eq]
    _ = Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
            {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) ≫
            projectiveChartMap S (ULift.{u} (Fin 2)) j) := by
      rw [Category.assoc, projectiveCoeffMap_chart]
    _ = (Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
            {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.map f))) ≫
            projectiveChartMap S (ULift.{u} (Fin 2)) j := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv S
            {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom)) ≫
            projectiveChartMap S (ULift.{u} (Fin 2)) j :=
      congrArg (fun h => h ≫ projectiveChartMap S (ULift.{u} (Fin 2)) j)
        (spec_unique_coeff (σ := {i : ULift.{u} (Fin 2) // i ≠ j}) f)
    _ = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
          projectiveLinePolynomialChart S j := by rw [Category.assoc, ← polynomial_chart_eq]

/-- The negative simple-root chart uses the polynomial coordinate whose image
is the additive-group generator. -/
theorem simpleNegativeChart_polynomial {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) (i : G.rootBase.support) :
    (simpleNegativeChart G i).left ≫ (simpleSchubertIso G i).hom.left =
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) ≫
          projectiveLinePolynomialChart K ⟨1⟩ := by
  exact (left_comp_eq _ _ _ (simpleSchubertIso_negative G i)).trans
    (projectiveLineChart_polynomial K ⟨1⟩)

-- GAP: C6-STAGE. Apply the two chart-coordinate certificates to the retained
-- simple-fibre comparison and chosen Schubert closed immersion. Retain the
-- section over the original field and its zero-coordinate equation on the
-- negative chart, and use its nilpotence relation and empty positive-chart pullback
-- to retain the fixed exponent and the same full intersection.

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem iso_chart_cover {P C A B : Scheme.{u}} (E : P ≅ C)
    (o : A ⟶ P) (z : B ⟶ P)
    (hc : ∀ x : P, x ∈ Set.range o ∨ x ∈ Set.range z) (x : C) :
    x ∈ Set.range (o ≫ E.hom) ∨ x ∈ Set.range (z ≫ E.hom) := by
  rcases hc (E.inv x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · left
    refine ⟨y, ?_⟩
    rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, E.inv_hom_id]
    rfl
  · right
    refine ⟨y, ?_⟩
    rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, E.inv_hom_id]
    rfl

/-- The map of intersections induced by a chart on the curve. -/
def intersectionChartMap {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    pullback (o ≫ d) j ⟶ pullback d j :=
  pullback.lift (pullback.fst (o ≫ d) j ≫ o) (pullback.snd (o ≫ d) j)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The intersection chart map retains its first projection. -/
theorem intersectionChartMap_fst {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    intersectionChartMap d j o ≫ pullback.fst d j = pullback.fst (o ≫ d) j ≫ o :=
  pullback.lift_fst _ _ _

/-- An intersection chart map forms the associated Cartesian square. -/
theorem intersectionChartMap_cartesian {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    IsPullback (intersectionChartMap d j o) (pullback.fst (o ≫ d) j)
      (pullback.fst d j) o := by
  have houter : IsPullback
      (intersectionChartMap d j o ≫ pullback.snd d j) (pullback.fst (o ≫ d) j) j (o ≫ d) := by
    rw [show intersectionChartMap d j o ≫ pullback.snd d j =
      pullback.snd (o ≫ d) j from pullback.lift_snd _ _ _]
    exact (IsPullback.of_hasPullback (o ≫ d) j).flip
  exact houter.of_right (intersectionChartMap_fst d j o) (IsPullback.of_hasPullback d j).flip

private theorem first_chart_isIso {C A B I Z W : Scheme.{u}}
    (f : I ⟶ C) (o : A ⟶ C) (z : B ⟶ C) [IsOpenImmersion o]
    (q : Z ⟶ I) (p : Z ⟶ A) (q' : W ⟶ I) (p' : W ⟶ B)
    (h : IsPullback q p f o) (h' : IsPullback q' p' f z)
    (hc : ∀ x : C, x ∈ Set.range o ∨ x ∈ Set.range z)
    (he : IsEmpty W) : IsIso q := by
  let : IsOpenImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip inferInstance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top q
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  rcases hc (f x) with ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback h x a ha.symm
    exact ⟨w, hw⟩
  · obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback h' x b hb.symm
    exact (he.false w).elim

/-- An intersection chart map retains its base projection. -/
theorem intersectionChartMap_base {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A S : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C)
    (b : C ⟶ S) (a : A ⟶ S) (ho : o ≫ b = a) :
    intersectionChartMap d j o ≫ (pullback.fst d j ≫ b) =
      pullback.fst (o ≫ d) j ≫ a := by
  rw [← Category.assoc, intersectionChartMap_fst, Category.assoc, ho]

/-- A chart transported along a base isomorphism retains its base map. -/
theorem intersectionChartIso_base {T : Type*} [Category T] {S A : T}
    {P C : Over S} (E : P ≅ C) (o : A ⟶ P.left) (a : A ⟶ S)
    (ho : o ≫ P.hom = a) : (o ≫ E.hom.left) ≫ C.hom = a := by
  rw [Category.assoc, E.hom.w]
  exact ho

private theorem inverse_factor_base {T : Type*} [Category T] {Z I A S : T}
    (q : Z ⟶ I) [IsIso q] (p : Z ⟶ A) (b : I ⟶ S) (a : A ⟶ S)
    (h : q ≫ b = p ≫ a) : ((asIso q).inv ≫ p) ≫ a = b := by
  rw [Category.assoc, ← h]
  exact (asIso q).inv_hom_id_assoc b

/-- Pullback of a coordinate commutes with a coefficient-ring map. -/
theorem intersectionChart_coordinate_comp {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of B)) (f : A →+* B) (r : A) :
    (c ≫ Spec.map (CommRingCat.ofHom f)).appTop
        ((Scheme.ΓSpecIso (.of A)).inv r) =
      c.appTop ((Scheme.ΓSpecIso (.of B)).inv (f r)) := by
  have h := congrArg (fun a : CommRingCat.of A ⟶ Γ(Spec (.of B), ⊤) => a r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  change (Scheme.ΓSpecIso (.of B)).inv (f r) =
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of A)).inv r) at h
  rw [Scheme.Hom.comp_appTop]
  exact congrArg (fun t => c.appTop t) h.symm

private theorem inverse_coordinate_pow {A : Type u} [CommRing A]
    {I Z : Scheme.{u}} (q : Z ⟶ I) [IsIso q] (p : Z ⟶ Spec (.of A))
    (r : A) (N : ℕ)
    (hnil : (p.appTop ((Scheme.ΓSpecIso (.of A)).inv r)) ^ N = 0) :
    (((asIso q).inv ≫ p).appTop ((Scheme.ΓSpecIso (.of A)).inv r)) ^ N = 0 := by
  rw [Scheme.Hom.comp_appTop]
  change ((asIso q).inv.appTop (p.appTop ((Scheme.ΓSpecIso (.of A)).inv r))) ^ N = 0
  rw [← map_pow, hnil, map_zero]

end SchubertGeometry
