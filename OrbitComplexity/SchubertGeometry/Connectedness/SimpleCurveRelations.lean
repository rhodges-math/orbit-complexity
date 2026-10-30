import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RestrictedCurveRetention
import OrbitComplexity.SchubertGeometry.Normality.Curves.ClosedCurveComparison

set_option autoImplicit false

/-! # Coefficient relations of a restricted simple-curve intersection

The negative-chart factorization of the simple-curve intersection is transported
through the specified projective-line and Schubert coefficient comparisons.
The two relations are retained in the rings of those same chart pullbacks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting Polynomial
open scoped TensorProduct

namespace SchubertGeometry

universe u v

private theorem simultaneous_relations
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {P M : Type u} [CommRing P] [CommRing M] [Algebra S P] [Algebra S M]
    (x : P) (N : ℕ)
    (hn : (1 : K) ⊗ₜ[S] (x ^ N) = 0)
    (he : (1 : K) ⊗ₜ[S] (1 : M) = 0) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ (1 : R) ⊗ₜ[S] (x ^ N) = 0 ∧ (1 : R) ⊗ₜ[S] (1 : M) = 0 := by
  let B : Bool → Type u
    | false => M
    | true => P
  let (b : Bool) : CommRing (B b) := by
    cases b
    · exact inferInstanceAs (CommRing M)
    · exact inferInstanceAs (CommRing P)
  let (b : Bool) : Algebra S (B b) := by
    cases b
    · exact inferInstanceAs (Algebra S M)
    · exact inferInstanceAs (Algebra S P)
  let z : ∀ b : Bool, B b := fun b => by
    cases b
    · exact (1 : M)
    · exact x ^ N
  have hz : ∀ b : Bool, (1 : K) ⊗ₜ[S] z b = 0 := by
    intro b
    cases b
    · exact he
    · exact hn
  obtain ⟨R, hSR, hR, hzero⟩ := exists_retained_zero_relations S hS B z hz
  let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  exact ⟨R, hSR, hR, hzero true, hzero false⟩

/-- The nilpotence exponent and emptiness of the other affine chart of one
specified intersection are retained together over one coefficient enlargement. -/
theorem exists_restricted_chart_relations
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
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
    let o : (n : Fin 2) → (Spec (.of S[X]) ⟶ C.left) := fun n =>
      projectiveLinePolynomialChart S ⟨n⟩ ≫ E.hom.left
    let Z : Fin 2 → Scheme.{u} := fun n => pullback (o n ≫ d.left) j.left
    let p := fun n : Fin 2 => pullback.fst (o n ≫ d.left) j.left
    let a := fun n : Fin 2 => p n ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X]))
    let _ : Algebra S Γ(Z 1, ⊤) :=
      ((a 1).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let _ : Algebra S Γ(Z 0, ⊤) :=
      ((a 0).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧
      (1 : R) ⊗ₜ[S]
        (((p 1).appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) ^ N) = 0 ∧
      (1 : R) ⊗ₜ[S] (1 : Γ(Z 0, ⊤)) = 0 := by
  intro o Z p a inst₁ inst₀
  exact simultaneous_relations S hS _ N
    (curveIntersection_nil_relation S E d j bK qI hI β hproj N hnil)
    (curveIntersection_other_relation S E d j bK qI hI β hproj N hN hnil)

-- GAP: C6-STAGE. Instantiate the coefficient comparison and polynomial
-- factorization with the retained simple-fibre isomorphism and the restricted
-- branch of simpleCurve_finite_cases. Retain its section at a stage above the
-- relation enlargement, identify the scalar pullbacks of these same two chart
-- rings, and apply curveIntersection_negative_gc to that stage intersection.

private theorem left_comp_eq {T : Type*} [Category T] {B : T}
    {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hh : f ≫ g = h) : f.left ≫ g.left = h.left :=
  congrArg (fun k : X ⟶ Z => k.left) hh

private theorem factor_chart {T : Type*} [Category T]
    {I A C P V : T} (c : I ⟶ A) (n : A ⟶ C) (f : I ⟶ C)
    (e : C ⟶ P) (g : A ⟶ V) (o : V ⟶ P)
    (hc : c ≫ n = f) (hn : n ≫ e = g ≫ o) :
    f ≫ e = (c ≫ g) ≫ o := by
  rw [← hc, Category.assoc, hn, ← Category.assoc]

private theorem projection_factor {T : Type*} [Category T]
    {I IK C CK P PK A AK : T}
    (qI : IK ⟶ I) (f : I ⟶ C) (fK : IK ⟶ CK) (qC : CK ⟶ C)
    (eK : CK ⟶ PK) (κP : PK ⟶ P) (e : P ⟶ C)
    (β : IK ⟶ AK) (κA : AK ⟶ A) (o : A ⟶ P) (oK : AK ⟶ PK)
    (hq : qI ≫ f = fK ≫ qC) (hC : qC = (eK ≫ κP) ≫ e)
    (hf : fK ≫ eK = β ≫ oK) (ho : oK ≫ κP = κA ≫ o) :
    qI ≫ f = (β ≫ κA) ≫ (o ≫ e) := by
  calc
    qI ≫ f = fK ≫ qC := hq
    _ = fK ≫ ((eK ≫ κP) ≫ e) := by rw [hC]
    _ = ((fK ≫ eK) ≫ κP) ≫ e := by simp only [Category.assoc]
    _ = ((β ≫ oK) ≫ κP) ≫ e := by rw [hf]
    _ = (β ≫ κA) ≫ (o ≫ e) := by rw [Category.assoc β oK κP, ho]; simp only [Category.assoc]

private theorem comp_coordinate {A B : Type u} [CommRing A] [CommRing B]
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

private theorem mapped_nilpotence {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} (f : A →+* B) (c : X ⟶ Spec (.of B))
    (β : X ⟶ Spec (.of A)) (hβ : β = c ≫ Spec.map (CommRingCat.ofHom f))
    (x : A) (y : B) (hxy : f x = y) (N : ℕ)
    (h : (c.appTop ((Scheme.ΓSpecIso (.of B)).inv y)) ^ N = 0) :
    (β.appTop ((Scheme.ΓSpecIso (.of A)).inv x)) ^ N = 0 := by
  have hc : β.appTop ((Scheme.ΓSpecIso (.of A)).inv x) =
      c.appTop ((Scheme.ΓSpecIso (.of B)).inv y) :=
    (congrArg (fun k : X ⟶ Spec (.of A) =>
      k.appTop ((Scheme.ΓSpecIso (.of A)).inv x)) hβ).trans
        ((comp_coordinate c f x).trans
          (congrArg (fun z : B => c.appTop ((Scheme.ΓSpecIso (.of B)).inv z)) hxy))
  exact (congrArg (fun z : Γ(X, ⊤) => z ^ N) hc).trans h

private theorem relations_of_comparisons
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    {CK YK FK : Scheme.{u}}
    (cK : CK ⟶ Spec (.of K)) (yK : YK ⟶ Spec (.of K))
    (tK : FK ⟶ Spec (.of K)) (dK : CK ⟶ FK) (jK : YK ⟶ FK)
    (hdK : dK ≫ tK = cK) (hjK : jK ≫ tK = yK)
    (qC : CK ⟶ C.left) (qY : YK ⟶ Y.left) (qF : FK ⟶ F.left)
    (hC : IsPullback qC cK C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY yK Y.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF tK F.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hd : dK ≫ qF = qC ≫ d.left) (hj : jK ≫ qF = qY ≫ j.left)
    (eK : CK ⟶ projectiveScheme K (ULift.{u} (Fin 2)))
    (hcoeff : qC = (eK ≫ projectiveCoeffMap (ULift.{u} (Fin 2))
      (algebraMap S K)) ≫ E.hom.left)
    (β : pullback dK jK ⟶ Spec (.of K[X]))
    (hfactor : pullback.fst dK jK ≫ eK =
      β ≫ projectiveLinePolynomialChart K ⟨1⟩)
    (N : ℕ) (hN : 0 < N)
    (hnil : (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) ^ N = 0) :
    let o : (n : Fin 2) → (Spec (.of S[X]) ⟶ C.left) := fun n =>
      projectiveLinePolynomialChart S ⟨n⟩ ≫ E.hom.left
    let Z : Fin 2 → Scheme.{u} := fun n => pullback (o n ≫ d.left) j.left
    let p := fun n : Fin 2 => pullback.fst (o n ≫ d.left) j.left
    let a := fun n : Fin 2 => p n ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X]))
    let _ : Algebra S Γ(Z 1, ⊤) :=
      ((a 1).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let _ : Algebra S Γ(Z 0, ⊤) :=
      ((a 0).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧
      (1 : R) ⊗ₜ[S]
        (((p 1).appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) ^ N) = 0 ∧
      (1 : R) ⊗ₜ[S] (1 : Γ(Z 0, ⊤)) = 0 := by
  have h := paired_model_scalar_pullback
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) cK yK tK
    C.hom Y.hom F.hom dK jK d.left j.left hdK hjK d.w j.w
    qC qY qF hC hY hF hd hj
  have hp := projection_factor _ (pullback.fst d.left j.left) (pullback.fst dK jK)
    qC eK _ E.hom.left β _ _ _ h.2.1 hcoeff hfactor
    (projectivePolynomialChart_coeff (algebraMap S K) ⟨1⟩)
  exact exists_restricted_chart_relations S hS E d j
    (pullback.fst dK jK ≫ cK) _ h.1 β hp N hN hnil

/-- The restricted simple-curve alternative retains its exponent and empty
opposite chart in the two chart rings of the specified Schubert intersection. -/
theorem simpleCurve_restricted_relations
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (w v : G.weylGroup) (i : G.rootBase.support)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    (qC : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶ C.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hd : (simpleSchubertCurve G w i).left ≫ qF = qC ≫ d.left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hcoeff : qC = simpleCurveCoefficientMap S G i ≫ E.hom.left)
    (c : Over.mk (pullback.fst (simpleSchubertCurve G w i).left
      (schubertInclusion G v).left ≫
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec) ⟶
          (additiveVariety K).toOver)
    (hc : c ≫ simpleNegativeChart G i = Over.homMk
      (pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left) rfl)
    (N : ℕ) (hN : 0 < N)
    (hnil : (c.left.appTop
      ((Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv
        (SymmetricAlgebra.ι K K 1))) ^ N = 0) :
    let o : (n : Fin 2) → (Spec (.of S[X]) ⟶ C.left) := fun n =>
      projectiveLinePolynomialChart S ⟨n⟩ ≫ E.hom.left
    let Z : Fin 2 → Scheme.{u} := fun n => pullback (o n ≫ d.left) j.left
    let p := fun n : Fin 2 => pullback.fst (o n ≫ d.left) j.left
    let a := fun n : Fin 2 => p n ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X]))
    let _ : Algebra S Γ(Z 1, ⊤) :=
      ((a 1).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let _ : Algebra S Γ(Z 0, ⊤) :=
      ((a 0).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧
      (1 : R) ⊗ₜ[S]
        (((p 1).appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) ^ N) = 0 ∧
      (1 : R) ⊗ₜ[S] (1 : Γ(Z 0, ⊤)) = 0 := by
  let g : K[X] →+* SymmetricAlgebra K K :=
    (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom
  let β := c.left ≫ Spec.map (CommRingCat.ofHom g)
  have hf := factor_chart c.left (simpleNegativeChart G i).left
    (pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left)
    (simpleSchubertIso G i).hom.left (Spec.map (CommRingCat.ofHom g))
    (projectiveLinePolynomialChart K ⟨1⟩) (left_comp_eq c _ _ hc)
    (simpleNegativeChart_polynomial G i)
  have hβ : (β.appTop ((Scheme.ΓSpecIso (.of K[X])).inv Polynomial.X)) ^ N = 0 :=
    mapped_nilpotence g c.left β rfl Polynomial.X (SymmetricAlgebra.ι K K 1)
      (Polynomial.aeval_X (SymmetricAlgebra.ι K K 1)) N hnil
  exact relations_of_comparisons S hS E d j
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
    (schubertVariety G v).toSpec (flagVariety G).toSpec
    (simpleSchubertCurve G w i).left (schubertInclusion G v).left
    (simpleSchubertCurve G w i).w (schubertInclusion G v).w
    qC qY qF hC hY hF hd hj (simpleSchubertIso G i).hom.left hcoeff β hf N hN hβ

-- GAP: C6-STAGE. Retain the original section at a stage above the simultaneous
-- chart relations. Identify both scalar chart pullbacks on that same stage
-- intersection, and apply curveIntersection_negative_gc there.

end SchubertGeometry
