import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CurveIntersectionCoordinates
import OrbitComplexity.SchubertGeometry.Connectedness.ElementaryCurves
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteRelations
import Mathlib.AlgebraicGeometry.PullbackCarrier

set_option autoImplicit false

/-! # Nilpotent charts of a closed curve intersection

The two affine charts are pullbacks on a specified closed intersection. If the
second chart is empty, the first chart is isomorphic to that intersection. A
nilpotence relation and a section then give connected geometric fibres.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open FrobeniusSplitting Polynomial
open scoped TensorProduct

namespace SchubertGeometry

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem mono_scalar_square {T : Type*} [Category T]
    {I Z IK S K : T} (a : I ⟶ S) (z : Z ⟶ I) [Mono z]
    (κ : K ⟶ S) (b : IK ⟶ K) (q : IK ⟶ I)
    (h : IsPullback q b a κ) (l : IK ⟶ Z) (hl : l ≫ z = q) :
    IsPullback l b (z ≫ a) κ := by
  have hw : l ≫ (z ≫ a) = b ≫ κ := by rw [← Category.assoc, hl, h.w]
  refine IsPullback.mk' hw ?_ ?_
  · intro W f g hf hg
    apply h.hom_ext
    · simpa only [Category.assoc, hl] using congrArg (fun t => t ≫ z) hf
    · exact hg
  · intro W f k hfk
    let v := h.lift (f ≫ z) k (by simpa only [Category.assoc] using hfk)
    have hv : v ≫ l = f := by
      apply (cancel_mono z).mp
      rw [Category.assoc, hl]
      exact h.lift_fst _ _ _
    exact ⟨v, hv, h.lift_snd _ _ _⟩

private theorem scalar_nilpotent_relation {S K : Type u} [CommRing S] [CommRing K]
    [Algebra S K] {Z ZK : Scheme.{u}} [IsAffine Z]
    (b : Z ⟶ Spec (.of S)) (bK : ZK ⟶ Spec (.of K)) (q : ZK ⟶ Z)
    (h : IsPullback q bK b (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (x : Γ(Z, ⊤)) (N : ℕ) (hnil : (q.appTop x) ^ N = 0) :
    let _ : Algebra S Γ(Z, ⊤) :=
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : K) ⊗ₜ[S] (x ^ N) = 0 := by
  intro inst
  let _ : Algebra K Γ(ZK, ⊤) :=
    (bK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  obtain ⟨e, _, he, _⟩ := exists_affine_scalar_coordinates b bK q h
  apply e.injective
  rw [map_zero, he, map_pow, hnil]

private theorem scalar_empty_relation {S K : Type u} [CommRing S] [CommRing K]
    [Algebra S K] {Z ZK : Scheme.{u}} [IsAffine Z]
    (b : Z ⟶ Spec (.of S)) (bK : ZK ⟶ Spec (.of K)) (q : ZK ⟶ Z)
    (h : IsPullback q bK b (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : IsEmpty ZK) :
    let _ : Algebra S Γ(Z, ⊤) :=
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : K) ⊗ₜ[S] (1 : Γ(Z, ⊤)) = 0 := by
  intro inst
  let _ : Algebra K Γ(ZK, ⊤) :=
    (bK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have htop : (⊤ : ZK.Opens) = ⊥ := by
    ext x
    exact (he.false x).elim
  let : Subsingleton Γ(ZK, ⊤) := by rw [htop]; infer_instance
  obtain ⟨e, _, heq, _⟩ := exists_affine_scalar_coordinates b bK q h
  apply e.injective
  rw [map_zero, heq]
  exact Subsingleton.elim _ _

private theorem change_square_base {T : Type*} [Category T]
    {P X Y B : T} {q : P ⟶ X} {a : P ⟶ Y} {f g : X ⟶ B} {κ : Y ⟶ B}
    (h : IsPullback q a f κ) (hf : f = g) : IsPullback q a g κ := hf ▸ h

private theorem coefficient_chart_preimage {S K : Type u} [CommRing S] [CommRing K]
    (f : S →+* K) (j : ULift.{u} (Fin 2)) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ⁻¹ᵁ
        (projectiveLinePolynomialChart S j).opensRange =
      (projectiveLinePolynomialChart K j).opensRange := by
  rw [projectiveLinePolynomialChart_range, projectiveLinePolynomialChart_range,
    projectiveCoeffMap, Proj.map_preimage_basicOpen]
  congr 1
  exact MvPolynomial.map_X f j

private theorem coefficient_chart_square {S K : Type u} [CommRing S] [CommRing K]
    (f : S →+* K) (j : ULift.{u} (Fin 2)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
      (projectiveLinePolynomialChart K j) (projectiveLinePolynomialChart S j)
      (projectiveCoeffMap (ULift.{u} (Fin 2)) f) :=
  IsOpenImmersion.isPullback _ _ _ _ (projectivePolynomialChart_coeff f j)
    (coefficient_chart_preimage f j)

private theorem nilpotent_positive_empty {K : Type u} [CommRing K]
    {I : Scheme.{u}} (β : I ⟶ Spec (.of K[X])) (N : ℕ) (hN : 0 < N)
    (hnil : (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) ^ N = 0) :
    IsEmpty (pullback (β ≫ projectiveLinePolynomialChart K ⟨1⟩)
      (projectiveLinePolynomialChart K ⟨0⟩) : Scheme.{u}) := by
  have hzero : β ⁻¹ᵁ (Spec (.of K[X])).basicOpen
      ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X) = ⊥ := by
    rw [Scheme.preimage_basicOpen_top,
      ← I.basicOpen_pow
        (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) hN,
      hnil, Scheme.basicOpen_zero]
  have hpre : (β ≫ projectiveLinePolynomialChart K ⟨1⟩) ⁻¹ᵁ
      (projectiveLinePolynomialChart K ⟨0⟩).opensRange = ⊥ := by
    rw [Scheme.Hom.comp_preimage, projectiveLinePolynomialChart_range,
      projectiveLinePolynomial_preimage K ⟨1⟩ ⟨0⟩ (by decide)]
    exact (congrArg (fun U : (Spec (.of K[X])).Opens => β ⁻¹ᵁ U)
      (basicOpen_eq_of_affine (Polynomial.X : K[X])).symm).trans hzero
  refine ⟨fun x => ?_⟩
  have hx : pullback.fst (β ≫ projectiveLinePolynomialChart K ⟨1⟩)
      (projectiveLinePolynomialChart K ⟨0⟩) x ∈
        (β ≫ projectiveLinePolynomialChart K ⟨1⟩) ⁻¹ᵁ
          (projectiveLinePolynomialChart K ⟨0⟩).opensRange := by
    refine ⟨(pullback.snd (β ≫ projectiveLinePolynomialChart K ⟨1⟩)
      (projectiveLinePolynomialChart K ⟨0⟩)) x, ?_⟩
    exact (congrArg (fun k => k x) (pullback.condition
      (f := β ≫ projectiveLinePolynomialChart K ⟨1⟩)
      (g := projectiveLinePolynomialChart K ⟨0⟩))).symm
  rw [hpre] at hx
  exact hx

private theorem chart_incidence_lift {T : Type*} [Category T] [HasPullbacks T]
    {I IK Z W C P PK A AK : T}
    (e : P ⟶ C) [Mono e] (f : I ⟶ C) (qI : IK ⟶ I)
    (qZ : Z ⟶ I) (p : Z ⟶ A) (o : A ⟶ P)
    (fK : IK ⟶ PK) (κP : PK ⟶ P)
    (κA : AK ⟶ A) (oK : AK ⟶ PK)
    (hA : IsPullback κA oK o κP)
    (hZ : qZ ≫ f = (p ≫ o) ≫ e)
    (hI : qI ≫ f = (fK ≫ κP) ≫ e)
    (t : W ⟶ Z) (s : W ⟶ IK) (ht : t ≫ qZ = s ≫ qI) :
    ∃ l : W ⟶ pullback fK oK, l ≫ pullback.fst fK oK = s := by
  have hc : (t ≫ p) ≫ o = (s ≫ fK) ≫ κP := by
    apply (cancel_mono e).mp
    calc
      ((t ≫ p) ≫ o) ≫ e = t ≫ ((p ≫ o) ≫ e) := by simp only [Category.assoc]
      _ = t ≫ (qZ ≫ f) := congrArg (fun k => t ≫ k) hZ.symm
      _ = (s ≫ qI) ≫ f := by rw [← Category.assoc, ht]
      _ = s ≫ ((fK ≫ κP) ≫ e) := by rw [Category.assoc, hI]
      _ = ((s ≫ fK) ≫ κP) ≫ e := by simp only [Category.assoc]
  let a := hA.lift (t ≫ p) (s ≫ fK) hc
  have ha : a ≫ oK = s ≫ fK := hA.lift_snd _ _ _
  exact ⟨pullback.lift s a ha.symm, pullback.lift_fst _ _ _⟩

private theorem chart_coordinate_eq {S K : Type u} [CommRing S] [CommRing K]
    {Z I : Scheme.{u}} (p : Z ⟶ Spec (.of S[X])) (l : I ⟶ Z)
    (β : I ⟶ Spec (.of K[X])) (f : S →+* K)
    (hl : l ≫ p = β ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) :
    l.appTop (p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) =
      β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X) := by
  have hc := intersectionChart_coordinate_comp β (Polynomial.mapRingHom f) Polynomial.X
  have hm : (Polynomial.mapRingHom f) Polynomial.X = Polynomial.X := Polynomial.map_X f
  rw [hm] at hc
  have hcomp := congrArg
    (fun a : Γ(Spec (.of S[X]), ⊤) ⟶ Γ(I, ⊤) =>
      a ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X))
    (Scheme.Hom.comp_appTop l p)
  exact hcomp.symm.trans
    ((congrArg (fun a : I ⟶ Spec (.of S[X]) =>
      a.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) hl).trans hc)

/-- The fixed exponent on the generic negative chart gives the same exponent
in the tensor extension of the closed intersection's negative chart ring. -/
theorem curveIntersection_nil_relation
    {K : Type u} [Field K] (S : Subalgebra ℤ K)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    {IK : Scheme.{u}} (bK : IK ⟶ Spec (.of K))
    (qI : IK ⟶ pullback d.left j.left)
    (hI : IsPullback qI bK (pullback.fst d.left j.left ≫ C.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (β : IK ⟶ Spec (.of K[X]))
    (hproj : qI ≫ pullback.fst d.left j.left =
      (β ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap S K)))) ≫
        (projectiveLinePolynomialChart S ⟨1⟩ ≫ E.hom.left))
    (N : ℕ)
    (hnil : (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) ^ N = 0) :
    let o := projectiveLinePolynomialChart S ⟨1⟩ ≫ E.hom.left
    let Z := pullback (o ≫ d.left) j.left
    let p := pullback.fst (o ≫ d.left) j.left
    let a := p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X]))
    let _ : Algebra S Γ(Z, ⊤) :=
      (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : K) ⊗ₜ[S]
      ((p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) ^ N) = 0 := by
  intro o Z p a inst
  let : IsAffine Z := isAffine_of_isAffineHom p
  let q := intersectionChartMap d.left j.left o
  have hc := intersectionChartMap_cartesian d.left j.left o
  let l := hc.lift qI
    (β ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap S K)))) hproj
  have hlq : l ≫ q = qI := hc.lift_fst _ _ _
  have hlp : l ≫ p =
      β ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap S K))) :=
    hc.lift_snd _ _ _
  let : IsOpenImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hc.flip inferInstance
  have ho : o ≫ C.hom =
      Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])) :=
    intersectionChartIso_base E (projectiveLinePolynomialChart S ⟨1⟩) _
      (projectiveLinePolynomialChart_base S ⟨1⟩)
  have ha : q ≫ (pullback.fst d.left j.left ≫ C.hom) = a :=
    intersectionChartMap_base d.left j.left o C.hom _ ho
  have hs := change_square_base
    (mono_scalar_square _ q _ bK qI hI l hlq) ha
  have hn : (l.appTop (p.appTop
      ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X))) ^ N = 0 := by
    rw [chart_coordinate_eq p l β (algebraMap S K) hlp]
    exact hnil
  exact scalar_nilpotent_relation a bK l hs _ N hn

/-- The other chart of the specified intersection is empty on the generic
fibre when its image lies at a nilpotent origin in the negative chart. -/
theorem curveIntersection_other_empty
    {K : Type u} [Field K] (S : Subalgebra ℤ K)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F)
    {IK : Scheme.{u}} (qI : IK ⟶ pullback d.left j.left)
    (β : IK ⟶ Spec (.of K[X]))
    (hproj : qI ≫ pullback.fst d.left j.left =
      ((β ≫ projectiveLinePolynomialChart K ⟨1⟩) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap S K)) ≫ E.hom.left)
    (N : ℕ) (hN : 0 < N)
    (hnil : (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) ^ N = 0) :
    let o := projectiveLinePolynomialChart S ⟨0⟩ ≫ E.hom.left
    let q : pullback (o ≫ d.left) j.left ⟶ pullback d.left j.left := pullback.lift
      (pullback.fst (o ≫ d.left) j.left ≫ o)
      (pullback.snd (o ≫ d.left) j.left)
      (by rw [Category.assoc]; exact pullback.condition (f := o ≫ d.left) (g := j.left))
    IsEmpty (pullback q qI : Scheme.{u}) := by
  intro o q
  let : IsEmpty (pullback (β ≫ projectiveLinePolynomialChart K ⟨1⟩)
      (projectiveLinePolynomialChart K ⟨0⟩) : Scheme.{u}) :=
    nilpotent_positive_empty β N hN hnil
  have hz : q ≫ pullback.fst d.left j.left =
      (pullback.fst (o ≫ d.left) j.left ≫ projectiveLinePolynomialChart S ⟨0⟩) ≫
        E.hom.left :=
    (intersectionChartMap_fst d.left j.left o).trans (Category.assoc _ _ _).symm
  obtain ⟨l, _⟩ := chart_incidence_lift E.hom.left
    (pullback.fst d.left j.left) qI q (pullback.fst (o ≫ d.left) j.left)
    (projectiveLinePolynomialChart S ⟨0⟩)
    (β ≫ projectiveLinePolynomialChart K ⟨1⟩)
    (projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap S K))
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap S K))))
    (projectiveLinePolynomialChart K ⟨0⟩)
    (coefficient_chart_square (algebraMap S K) ⟨0⟩) hz hproj
    (pullback.fst q qI) (pullback.snd q qI) (pullback.condition (f := q) (g := qI))
  exact ⟨fun x => isEmptyElim (l x)⟩

private theorem projection_coeff_eq {T : Type*} [Category T]
    {I C PK P A AK : T} (q : I ⟶ C) (β : I ⟶ AK)
    (a : AK ⟶ A) (o : A ⟶ P) (oK : AK ⟶ PK) (κ : PK ⟶ P) (e : P ⟶ C)
    (hchart : oK ≫ κ = a ≫ o) (h : q = (β ≫ a) ≫ (o ≫ e)) :
    q = ((β ≫ oK) ≫ κ) ≫ e := by
  calc
    q = (β ≫ a) ≫ (o ≫ e) := h
    _ = β ≫ (a ≫ o) ≫ e := by simp only [Category.assoc]
    _ = β ≫ (oK ≫ κ) ≫ e := by rw [hchart]
    _ = ((β ≫ oK) ≫ κ) ≫ e := by simp only [Category.assoc]

/-- The unit of the positive chart ring vanishes after extension to the original
field when the intersection has nilpotent negative coordinate. -/
theorem curveIntersection_other_relation
    {K : Type u} [Field K] (S : Subalgebra ℤ K)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    {IK : Scheme.{u}} (bK : IK ⟶ Spec (.of K))
    (qI : IK ⟶ pullback d.left j.left)
    (hI : IsPullback qI bK (pullback.fst d.left j.left ≫ C.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (β : IK ⟶ Spec (.of K[X]))
    (hproj : qI ≫ pullback.fst d.left j.left =
      (β ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap S K)))) ≫
        (projectiveLinePolynomialChart S ⟨1⟩ ≫ E.hom.left))
    (N : ℕ) (hN : 0 < N)
    (hnil : (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) ^ N = 0) :
    let o := projectiveLinePolynomialChart S ⟨0⟩ ≫ E.hom.left
    let Z := pullback (o ≫ d.left) j.left
    let p := pullback.fst (o ≫ d.left) j.left
    let a := p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X]))
    let _ : Algebra S Γ(Z, ⊤) :=
      (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : K) ⊗ₜ[S] (1 : Γ(Z, ⊤)) = 0 := by
  intro o Z p a inst
  let : IsAffine Z := isAffine_of_isAffineHom p
  let q := intersectionChartMap d.left j.left o
  have hproj' := projection_coeff_eq _ β _ _ _ _ E.hom.left
    (projectivePolynomialChart_coeff (algebraMap S K) ⟨1⟩) hproj
  have he : IsEmpty (pullback q qI : Scheme.{u}) :=
    curveIntersection_other_empty S E d j qI β hproj' N hN hnil
  have ho : o ≫ C.hom =
      Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])) :=
    intersectionChartIso_base E (projectiveLinePolynomialChart S ⟨0⟩) _
      (projectiveLinePolynomialChart_base S ⟨0⟩)
  have ha : q ≫ (pullback.fst d.left j.left ≫ C.hom) = a :=
    intersectionChartMap_base d.left j.left o C.hom _ ho
  have hs := change_square_base
    ((IsPullback.of_hasPullback q qI).paste_vert hI) ha
  exact scalar_empty_relation a (pullback.snd q qI ≫ bK) (pullback.fst q qI) hs he

end SchubertGeometry
