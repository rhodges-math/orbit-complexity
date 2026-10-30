import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.SimpleCurveRelations
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.SectionRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoordinates
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

set_option autoImplicit false

/-! # Connected fibres of the retained restricted curve intersection

The section and the two affine chart relations are retained on the specified
intersection. Scalar pullbacks of its chart rings determine the same stage
intersection, including its nilpotents.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting Polynomial Opposite SchubertGeometry.CellContraction
open scoped TensorProduct

namespace SchubertGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem section_post {T : Type*} [Category T] {B : T}
    {X Y : Over B} (f : X ⟶ Y) (s : B ⟶ X.left) (hs : s ≫ X.hom = 𝟙 B) :
    (s ≫ f.left) ≫ Y.hom = 𝟙 B := by
  rw [Category.assoc, f.w, hs]

private theorem chart_square {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C) :
    IsPullback (intersectionChartMap d j o) (pullback.fst (o ≫ d) j)
      (pullback.fst d j) o := by
  have hf : intersectionChartMap d j o ≫ pullback.fst d j =
      pullback.fst (o ≫ d) j ≫ o := pullback.lift_fst _ _ _
  have hs : intersectionChartMap d j o ≫ pullback.snd d j =
      pullback.snd (o ≫ d) j := pullback.lift_snd _ _ _
  have H : IsPullback (intersectionChartMap d j o ≫ pullback.snd d j)
      (pullback.fst (o ≫ d) j) j (o ≫ d) := by
    rw [hs]
    exact (IsPullback.of_hasPullback (o ≫ d) j).flip
  exact H.of_right hf (IsPullback.of_hasPullback d j).flip

private theorem chart_base {T : Type*} [Category T] [HasPullbacks T]
    {C F Y A S : T} (d : C ⟶ F) (j : Y ⟶ F) (o : A ⟶ C)
    (b : C ⟶ S) (a : A ⟶ S) (ho : o ≫ b = a) :
    intersectionChartMap d j o ≫ (pullback.fst d j ≫ b) =
      pullback.fst (o ≫ d) j ≫ a := by
  rw [← Category.assoc, show intersectionChartMap d j o ≫ pullback.fst d j =
    pullback.fst (o ≫ d) j ≫ o from pullback.lift_fst _ _ _, Category.assoc, ho]

private theorem iso_chart_base {T : Type*} [Category T] {S A : T}
    {P C : Over S} (E : P ≅ C) (o : A ⟶ P.left) (a : A ⟶ S)
    (ho : o ≫ P.hom = a) : (o ≫ E.hom.left) ≫ C.hom = a := by
  rw [Category.assoc, E.hom.w]
  exact ho

private theorem polynomial_chart_cover (R : Type u) [CommRing R]
    (x : projectiveScheme R (ULift.{u} (Fin 2))) :
    x ∈ Set.range (projectiveLinePolynomialChart R ⟨1⟩) ∨
      x ∈ Set.range (projectiveLinePolynomialChart R ⟨0⟩) := by
  have hcover : ∃ (j : ULift.{u} (Fin 2))
      (y : Spec (.of (MvPolynomial {i : ULift.{u} (Fin 2) // i ≠ j} R))),
      projectiveChartMap R (ULift.{u} (Fin 2)) j y = x :=
    Scheme.Cover.exists_eq (projectiveChartCover R (ULift.{u} (Fin 2))) x
  obtain ⟨j, y, hy⟩ := hcover
  let : IsOpenImmersion (projectiveLinePolynomialChart R j) :=
    projectiveLinePolynomialChart_open R j
  have hx : x ∈ (projectiveLinePolynomialChart R j).opensRange := by
    rw [projectiveLinePolynomialChart_range, ← projectiveChartMap_range]
    exact ⟨y, hy⟩
  rcases j with ⟨j⟩
  fin_cases j
  · exact Or.inr hx
  · exact Or.inl hx

private theorem intersection_cover {R : Type u} [CommRing R]
    {C F Y : Over (Spec (.of R))}
    (E : Over.mk (projectiveToSpec R (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) (x : (pullback d.left j.left : Scheme.{u})) :
    x ∈ Set.range (intersectionChartMap d.left j.left
        (projectiveLinePolynomialChart R ⟨1⟩ ≫ E.hom.left)) ∨
      x ∈ Set.range (intersectionChartMap d.left j.left
        (projectiveLinePolynomialChart R ⟨0⟩ ≫ E.hom.left)) := by
  let eC := (Over.forget (Spec (.of R))).mapIso E
  let f := pullback.fst d.left j.left
  have hpoint : eC.hom (eC.inv (f x)) = f x := by
    rw [← Scheme.Hom.comp_apply, eC.inv_hom_id]
    rfl
  rcases polynomial_chart_cover R (eC.inv (f x)) with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    have he : f x = (projectiveLinePolynomialChart R ⟨1⟩ ≫ E.hom.left) t := by
      rw [Scheme.Hom.comp_apply, ht]
      exact hpoint.symm
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (chart_square d.left j.left (projectiveLinePolynomialChart R ⟨1⟩ ≫ E.hom.left)) x t he
    exact ⟨z, hz⟩
  · right
    have he : f x = (projectiveLinePolynomialChart R ⟨0⟩ ≫ E.hom.left) t := by
      rw [Scheme.Hom.comp_apply, ht]
      exact hpoint.symm
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (chart_square d.left j.left (projectiveLinePolynomialChart R ⟨0⟩ ≫ E.hom.left)) x t he
    exact ⟨z, hz⟩

private theorem rebase_relation {S A : Type u} [CommRing S] [CommRing A]
    [Algebra S A] {Z : Scheme.{u}} (a b : Z ⟶ Spec (.of S)) (hab : a = b)
    (x : Γ(Z, ⊤)) :
    let _ : Algebra S Γ(Z, ⊤) :=
      (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : A) ⊗ₜ[S] x = 0 →
    let _ : Algebra S Γ(Z, ⊤) :=
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : A) ⊗ₜ[S] x = 0 := by
  subst b
  exact fun h => h

private theorem extend_zero {S R A P : Type u}
    [CommRing S] [CommRing R] [CommRing A] [CommRing P]
    [Algebra S R] [Algebra S A] [Algebra R A] [IsScalarTower S R A] [Algebra S P]
    (x : P) (hx : (1 : R) ⊗ₜ[S] x = 0) : (1 : A) ⊗ₜ[S] x = 0 := by
  let f : R ⊗[S] P →ₐ[S] A ⊗[S] P :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R A) (AlgHom.id S P)
  simpa only [f, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, map_zero]
    using congrArg f hx

private def comparisonIso {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {I IK : Scheme.{u}} (b : I ⟶ Spec (.of S)) (bK : IK ⟶ Spec (.of K))
    (q : IK ⟶ I)
    (h : IsPullback q bK b (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    Over.mk bK ≅ genericScalarModel S b :=
  Over.isoMk h.flip.isoPullback h.flip.isoPullback_hom_fst

private def scalar_cone_arrow {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {I : Scheme.{u}} (b : I ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (genericScalarModel S b).left ⟶ (stageScalarModel S b i).left :=
  (modelScalarCone S b).π.app (op i)

private theorem cone_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {I : Scheme.{u}} (b : I ⟶ Spec (.of S)) (i : CoefficientStage S) :
    scalar_cone_arrow S b i ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) b =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) b := by
  change pullback.lift _ _ _ ≫ pullback.snd _ b = _
  exact pullback.lift_snd _ _ _

private theorem composition_triangle {T : Type*} [Category T]
    {A B C D : T} (e : A ⟶ B) (p : B ⟶ C) (r : C ⟶ D)
    (q : B ⟶ D) (s : A ⟶ D) (hp : p ≫ r = q) (he : e ≫ q = s) :
    (e ≫ p) ≫ r = s :=
  (Category.assoc e p r).trans ((congrArg (fun f => e ≫ f) hp).trans he)

private theorem field_connected {R : Type u} [CommRing R] {X : Scheme.{u}}
    (b : X ⟶ Spec (.of R)) [GeometricallyConnected b]
    (L : Type u) [Field L] (ρ : R →+* L) :
    ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ)) b : Scheme.{u}) := by
  let : GeometricallyConnected (pullback.fst (Spec.map (CommRingCat.ofHom ρ)) b) :=
    inferInstance
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (f := pullback.fst (Spec.map (CommRingCat.ofHom ρ)) b)

private def restricted_stage_result
    {K : Type u} [Field K] (S : Subalgebra ℤ K)
    {I Z IK : Scheme.{u}} (b : I ⟶ Spec (.of S)) (q : Z ⟶ I) (x : Γ(Z, ⊤))
    (bK : IK ⟶ Spec (.of K)) (qI : IK ⟶ I)
    (σK : Spec (.of K) ⟶ IK) (N : ℕ) : Prop :=
    ∃ (k : CoefficientStage S)
      (σ : Spec (.of k.val) ⟶ (stageScalarModel S b k).left)
      (qK : IK ⟶ (stageScalarModel S b k).left),
      σ ≫ (stageScalarModel S b k).hom = 𝟙 _ ∧
      IsPullback qK bK (stageScalarModel S b k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qK ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b = qI ∧
      Spec.map (CommRingCat.ofHom (algebraMap k.val K)) ≫ σ = σK ≫ qK ∧
      ∃ e : (pullback q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b) :
            Scheme.{u}) ≅ (stageScalarModel S b k).left,
        e.hom = pullback.snd q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b) ∧
        (((pullback.fst q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b)).appTop x)
            ^ N = 0) ∧
        (σ ≫ e.inv).appTop ((pullback.fst q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b)).appTop x)
            = 0 ∧
        GeometricallyConnected (stageScalarModel S b k).hom ∧
        ∀ (L : Type u) [Field L] (ρ : k.val →+* L),
          ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
            (stageScalarModel S b k).hom : Scheme.{u})

private theorem stage_from_relations
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    [LocallyOfFinitePresentation (pullback.fst d.left j.left ≫ C.hom)]
    {IK : Scheme.{u}} (bK : IK ⟶ Spec (.of K))
    (qI : IK ⟶ pullback d.left j.left)
    (hI : IsPullback qI bK (pullback.fst d.left j.left ≫ C.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (σK : Spec (.of K) ⟶ IK) (hσK : σK ≫ bK = 𝟙 _)
    (N : ℕ) (hN : 0 < N) :
    let o : (n : Fin 2) → (Spec (.of S[X]) ⟶ C.left) := fun n =>
      projectiveLinePolynomialChart S ⟨n⟩ ≫ E.hom.left
    let Z : Fin 2 → Scheme.{u} := fun n => pullback (o n ≫ d.left) j.left
    let p := fun n : Fin 2 => pullback.fst (o n ≫ d.left) j.left
    let q := fun n : Fin 2 => intersectionChartMap d.left j.left (o n)
    let b := pullback.fst d.left j.left ≫ C.hom
    let a := fun n : Fin 2 => p n ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X]))
    let x := (p 1).appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)
    let _ : Algebra S Γ(Z 1, ⊤) :=
      ((a 1).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let _ : Algebra S Γ(Z 0, ⊤) :=
      ((a 0).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ (1 : R) ⊗ₜ[S] (x ^ N) = 0 ∧ (1 : R) ⊗ₜ[S] (1 : Γ(Z 0, ⊤)) = 0) →
    restricted_stage_result S b (q 1) x bK qI σK N := by
  intro o Z p q b a x inst₁ inst₀ hrelations
  obtain ⟨R, hSR, hR, hnR, heR⟩ := hrelations
  let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let start : CoefficientStage S := ⟨R, hR, hSR⟩
  let Eₖ : Over.mk bK ≅ genericScalarModel S b := comparisonIso S b bK qI hI
  let s : Spec (.of K) ⟶ (genericScalarModel S b).left := σK ≫ Eₖ.hom.left
  have hs : s ≫ (genericScalarModel S b).hom = 𝟙 _ := section_post Eₖ.hom σK hσK
  obtain ⟨k, hk, f, hf⟩ := exists_retained_sections S hS
    (fun _ : PUnit.{u+1} => pullback d.left j.left) (fun _ => b)
    (fun _ => s) (fun _ => hs) start
  let σ := stageOriginSection S (𝟙 _) (𝟙 _) (Category.id_comp _) k ≫ (f PUnit.unit).left
  have hσ : σ ≫ (stageScalarModel S b k).hom = 𝟙 _ := (hf PUnit.unit).2.1
  let qK : IK ⟶ (stageScalarModel S b k).left := Eₖ.hom.left ≫ scalar_cone_arrow S b k
  have hK : IsPullback qK bK (stageScalarModel S b k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    overIso_modelStage_cartesian S b k (Over.mk bK) Eₖ
  have hqK : qK ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b = qI := by
    exact composition_triangle Eₖ.hom.left (scalar_cone_arrow S b k) _ _ qI
      (cone_original S b k) hI.flip.isoPullback_hom_snd
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap k.val K)) ≫ σ = σK ≫ qK :=
    ((hf PUnit.unit).2.2).trans (Category.assoc _ _ _)
  let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let _ : Algebra R k.val := (Subalgebra.inclusion hk).toAlgebra
  let _ : IsScalarTower S R k.val := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hnₖ : (1 : k.val) ⊗ₜ[S] (x ^ N) = 0 := extend_zero (x ^ N) hnR
  have heₖ : (1 : k.val) ⊗ₜ[S] (1 : Γ(Z 0, ⊤)) = 0 := extend_zero _ heR
  have hbase : ∀ n : Fin 2, q n ≫ b = a n := by
    intro n
    exact chart_base d.left j.left (o n) C.hom _
      (iso_chart_base E (projectiveLinePolynomialChart S ⟨n⟩) _
        (projectiveLinePolynomialChart_base S ⟨n⟩))
  let _ : IsAffine (Z 1) := isAffine_of_isAffineHom (p 1)
  let _ : IsAffine (Z 0) := isAffine_of_isAffineHom (p 0)
  let _ : IsOpenImmersion (q 1) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (chart_square d.left j.left (o 1)).flip inferInstance
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let qstage := pullback.snd κ b
  have hstage : IsPullback qstage (stageScalarModel S b k).hom b κ :=
    (IsPullback.of_hasPullback κ b).flip
  have hnil :
      let _ : Algebra S Γ(Z 1, ⊤) :=
        ((q 1 ≫ b).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
      (1 : k.val) ⊗ₜ[S] (x ^ N) = 0 :=
    rebase_relation (a 1) (q 1 ≫ b) (hbase 1).symm (x ^ N) hnₖ
  have hempty :
      let _ : Algebra S Γ(Z 0, ⊤) :=
        ((q 0 ≫ b).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
      (1 : k.val) ⊗ₜ[S] (1 : Γ(Z 0, ⊤)) = 0 :=
    rebase_relation (a 0) (q 0 ≫ b) (hbase 0).symm _ heₖ
  obtain ⟨e, he, hpow, hzero, hgc⟩ := scalar_cover_gc b (stageScalarModel S b k).hom qstage
    hstage (q 1) (q 0) (p 1) (hbase 1).symm (intersection_cover E d j) N hN
    hnil hempty σ hσ
  let _ : GeometricallyConnected (stageScalarModel S b k).hom := hgc
  exact ⟨k, σ, qK, hσ, hK, hqK, hcomp, e, he, hpow, hzero, hgc,
    fun L _ ρ => field_connected _ L ρ⟩

/-- The restricted simple-curve alternative, with its original section, has
connected field fibres on a scalar stage of the same closed intersection.
Both chart rings, the original coefficient map, and the fixed exponent are retained. -/
theorem exists_simpleCurve_restricted_gc
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (w v : G.weylGroup) (i : G.rootBase.support)
    {C F Y : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    [LocallyOfFinitePresentation (pullback.fst d.left j.left ≫ C.hom)]
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
        (SymmetricAlgebra.ι K K 1))) ^ N = 0)
    (σK : Spec (.of K) ⟶ pullback (simpleSchubertCurve G w i).left
      (schubertInclusion G v).left)
    (hσK : σK ≫ (pullback.fst (simpleSchubertCurve G w i).left
      (schubertInclusion G v).left ≫
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec) = 𝟙 _) :
    let o := projectiveLinePolynomialChart S ⟨1⟩ ≫ E.hom.left
    let p := pullback.fst (o ≫ d.left) j.left
    let q : pullback (o ≫ d.left) j.left ⟶ pullback d.left j.left :=
      pullback.lift (p ≫ o) (pullback.snd (o ≫ d.left) j.left)
        ((Category.assoc p o d.left).trans
          (pullback.condition (f := o ≫ d.left) (g := j.left)))
    let x := p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)
    let b := pullback.fst d.left j.left ≫ C.hom
    let qI := pullback.map (simpleSchubertCurve G w i).left (schubertInclusion G v).left
      d.left j.left qC qY qF hd hj
    ∃ (k : CoefficientStage S)
      (σ : Spec (.of k.val) ⟶ (stageScalarModel S b k).left)
      (qK : pullback (simpleSchubertCurve G w i).left (schubertInclusion G v).left ⟶
        (stageScalarModel S b k).left),
      σ ≫ (stageScalarModel S b k).hom = 𝟙 _ ∧
      IsPullback qK
        (pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left ≫
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec)
        (stageScalarModel S b k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qK ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b = qI ∧
      Spec.map (CommRingCat.ofHom (algebraMap k.val K)) ≫ σ = σK ≫ qK ∧
      ∃ e : (pullback q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b) :
            Scheme.{u}) ≅ (stageScalarModel S b k).left,
        e.hom = pullback.snd q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b) ∧
        (((pullback.fst q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b)).appTop x)
            ^ N = 0) ∧
        (σ ≫ e.inv).appTop ((pullback.fst q (pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b)).appTop x)
            = 0 ∧
        GeometricallyConnected (stageScalarModel S b k).hom ∧
        ∀ (L : Type u) [Field L] (ρ : k.val →+* L),
          ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
            (stageScalarModel S b k).hom : Scheme.{u}) := by
  have h := paired_model_scalar_pullback
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
    (schubertVariety G v).toSpec (flagVariety G).toSpec
    C.hom Y.hom F.hom (simpleSchubertCurve G w i).left (schubertInclusion G v).left
    d.left j.left (simpleSchubertCurve G w i).w (schubertInclusion G v).w d.w j.w
    qC qY qF hC hY hF hd hj
  exact stage_from_relations S hS E d j
    (pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left ≫
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec)
    _ h.1 σK hσK N hN
    (simpleCurve_restricted_relations S hS G w v i E d j
      qC qY qF hC hY hF hd hj hcoeff c hc N hN hnil)

end SchubertGeometry
