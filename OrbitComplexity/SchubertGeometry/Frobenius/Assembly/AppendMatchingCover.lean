import OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarPolynomialSquare
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Flat.Basic
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # A common affine cover for append coframes

The matching charts and the polynomial charts have a common finite affine
refinement. Its coordinate maps retain the two chart projections and their
scalar comparison.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement

/-- Intersect the two open covers while retaining the index of each chart. -/
def appendCommonCover {Y : Scheme.{u}} (W V : Y.OpenCover.{u}) : Y.OpenCover.{u} :=
  W.bind fun w => V.pullback₁ (W.f w)

/-- The common refinement of two finite covers has finitely many charts. -/
instance {Y : Scheme.{u}} (W V : Y.OpenCover.{u}) [Finite W.I₀] [Finite V.I₀] :
    Finite (appendCommonCover W V).I₀ :=
  inferInstanceAs (Finite (Σ _ : W.I₀, V.I₀))

/-- A common chart of affine covers of a separated scheme is affine. -/
instance {Y : Scheme.{u}} [Y.IsSeparated] (W V : Y.OpenCover.{u})
    [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (l : (appendCommonCover W V).I₀) : IsAffine ((appendCommonCover W V).X l) := by
  let w : W.I₀ := l.1
  let v : V.I₀ := l.2
  let : IsAffine (W.X w) := inferInstance
  let : IsAffine (V.X v) := inferInstance
  exact affine_fibre_product (W.f w) (V.f v)

/-- The first projection of a common chart into its matching chart. -/
def appendCommonLeft {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (l : (appendCommonCover W V).I₀) :
    (appendCommonCover W V).X l ⟶ W.X l.1 :=
  pullback.fst (W.f l.1) (V.f l.2)

/-- The second projection of a common chart into its polynomial chart. -/
def appendCommonRight {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (l : (appendCommonCover W V).I₀) :
    (appendCommonCover W V).X l ⟶ V.X l.2 :=
  pullback.snd (W.f l.1) (V.f l.2)

/-- The first projection followed by the matching chart is the refined chart. -/
theorem appendCommonLeft_map {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (l : (appendCommonCover W V).I₀) :
    appendCommonLeft W V l ≫ W.f l.1 = (appendCommonCover W V).f l := rfl

/-- The second projection followed by the polynomial chart is the refined chart. -/
theorem appendCommonRight_map {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (l : (appendCommonCover W V).I₀) :
    appendCommonRight W V l ≫ V.f l.2 = (appendCommonCover W V).f l :=
  (pullback.condition (f := W.f l.1) (g := V.f l.2)).symm

/-- The projection to the matching chart is an open immersion. -/
instance {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (l : (appendCommonCover W V).I₀) : IsOpenImmersion (appendCommonLeft W V l) := by
  unfold appendCommonLeft
  exact MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (W.f l.1) (V.f l.2)).flip (V.map_prop l.2)

/-- The projection to the polynomial chart is an open immersion. -/
instance {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (l : (appendCommonCover W V).I₀) : IsOpenImmersion (appendCommonRight W V l) := by
  unfold appendCommonRight
  exact MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (W.f l.1) (V.f l.2)) (W.map_prop l.1)

private theorem lifted_chart_square {B A X P Q : Scheme.{u}}
    (u : B ⟶ A) (v : B ⟶ X) (k : A ⟶ P)
    (c : P ⟶ Q) (m : X ⟶ Q)
    (h : u ≫ k ≫ c = v ≫ m)
    {PK : Scheme.{u}} (a : PK ⟶ P) (b : PK ⟶ X)
    (H : IsPullback a b c m) :
    ∃ kK : B ⟶ PK, kK ≫ a = u ≫ k ∧ kK ≫ b = v := by
  exact ⟨H.lift (u ≫ k) v (by simpa only [Category.assoc] using h),
    H.lift_fst _ _ _, H.lift_snd _ _ _⟩

private theorem coordinate_scalar_square {C CK P PK : Scheme.{u}}
    [IsAffine C] [IsAffine CK]
    (u : CK ⟶ C) (k : C ⟶ P) (kK : CK ⟶ PK)
    (v : PK ⟶ P) (h : kK ≫ v = u ≫ k) :
    Spec.map u.appTop ≫ (C.isoSpec.inv ≫ k) = CK.isoSpec.inv ≫ kK ≫ v := by
  calc
    Spec.map u.appTop ≫ (C.isoSpec.inv ≫ k) =
        (Spec.map u.appTop ≫ C.isoSpec.inv) ≫ k := (Category.assoc _ _ _).symm
    _ = (CK.isoSpec.inv ≫ u) ≫ k :=
      congrArg (· ≫ k) (Scheme.isoSpec_inv_naturality u)
    _ = CK.isoSpec.inv ≫ (u ≫ k) := Category.assoc _ _ _
    _ = CK.isoSpec.inv ≫ (kK ≫ v) := congrArg (CK.isoSpec.inv ≫ ·) h.symm

private theorem scalar_chart_lift {P A Y X B S : Scheme.{u}}
    (κ : P ⟶ A) (p : P ⟶ B) (a : A ⟶ S) (β : B ⟶ S)
    (HP : IsPullback κ p a β)
    (q : Y ⟶ X) (y : Y ⟶ B) (x : X ⟶ S)
    (HY : IsPullback q y x β) (j : A ⟶ X) (hj : j ≫ x = a) :
    ∃ f : P ⟶ Y, IsPullback κ f j q ∧ f ≫ q = κ ≫ j ∧ f ≫ y = p := by
  have H : IsPullback p κ β (j ≫ x) := by
    rw [hj]
    exact HP.flip
  let f := HY.flip.lift p (κ ≫ j) (by rw [H.w, Category.assoc])
  have hf : IsPullback f κ q j := IsPullback.of_right' H HY.flip
  exact ⟨f, hf.flip, HY.flip.lift_snd _ _ _, HY.flip.lift_fst _ _ _⟩

private theorem chart_lift_unique {P A Y X B S : Scheme.{u}}
    (κ : P ⟶ A) (p : P ⟶ B) (β : B ⟶ S)
    (q : Y ⟶ X) (y : Y ⟶ B) (x : X ⟶ S)
    (HY : IsPullback q y x β) (j : A ⟶ X)
    (f g : P ⟶ Y) (hf : f ≫ q = κ ≫ j) (hg : g ≫ q = κ ≫ j)
    (hfp : f ≫ y = p) (hgp : g ≫ y = p) : f = g :=
  HY.hom_ext (hf.trans hg.symm) (hfp.trans hgp.symm)

private theorem flat_affine_coordinates {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of R)) [Flat f] :
    let : Algebra R Γ(X, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    Module.Flat R Γ(X, ⊤) := by
  let : Algebra R Γ(X, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  apply RingHom.flat_algebraMap_iff.mp
  exact (RingHom.Flat.of_bijective
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective).comp f.flat_appTop

private theorem scalar_coordinate_injective {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B] [Module.Flat R A]
    (hR : Function.Injective (algebraMap R K))
    (e : K ⊗[R] A ≃ₐ[K] B) (v : A →+* B)
    (he : ∀ x, e ((1 : K) ⊗ₜ[R] x) = v x) : Function.Injective v := by
  have hv : v = e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    exact (he x).symm
  rw [hv]
  exact e.injective.comp (Algebra.TensorProduct.includeRight_injective hR)

private theorem common_field_coordinates {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {X P : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of R)) [Smooth f]
    (t : P ⟶ Spec (.of K)) (q : P ⟶ X)
    (h : IsPullback q t f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    let : Algebra R Γ(X, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    let : Algebra K Γ(P, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    Module.Flat R Γ(X, ⊤) ∧ Function.Injective q.appTop.hom ∧
      ∃ e : K ⊗[R] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤),
        (∀ k, e (k ⊗ₜ[R] (1 : Γ(X, ⊤))) = algebraMap K Γ(P, ⊤) k) ∧
        (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
        ∀ k x, e (k ⊗ₜ[R] x) = algebraMap K Γ(P, ⊤) k * q.appTop.hom x := by
  let : Algebra R Γ(X, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let : Module.Flat R Γ(X, ⊤) := flat_affine_coordinates f
  obtain ⟨e, he, hq, htmul⟩ := exists_affine_scalar_coordinates f t q h
  exact ⟨inferInstance, scalar_coordinate_injective hR e q.appTop.hom hq,
    e, he, hq, htmul⟩

/-- Polynomial charts of a prescribed model extend to a cover of its scalar
model. The cover retains the old chart and structural projections. -/
theorem exists_append_scalar_cover {T R : Type u} [CommRing T] [CommRing R]
    [Algebra T R] {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of T)) (baseR : Y ⟶ Spec (.of R)) (q : Y ⟶ X)
    (hY : IsPullback q baseR base (Spec.map (CommRingCat.ofHom (algebraMap T R))))
    (U : X.OpenCover.{u}) [Finite U.I₀]
    (A : U.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra T (A j)]
    (eU : ∀ j, U.X j ≅ Spec (.of (Polynomial (A j))))
    (hU : ∀ j, ((eU j).inv ≫ U.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (A j))))) :
    ∃ (V : Y.OpenCover.{u}) (_hfinite : Finite V.I₀) (_haffine : ∀ j, IsAffine (V.X j))
      (index : V.I₀ ≃ U.I₀)
      (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (R ⊗[T] A (index j))))),
      (∀ j, IsPullback
        ((eV j).hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A (index j) →ₐ[T]
            R ⊗[T] A (index j)).toRingHom)))
        (V.f j) ((eU (index j)).inv ≫ U.f (index j)) q) ∧
      (∀ j, V.f j ≫ baseR = (eV j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] A (index j)))))) ∧
      ∀ j, V.f j ≫ q = (eV j).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A (index j) →ₐ[T]
            R ⊗[T] A (index j)).toRingHom)) ≫
          (eU (index j)).inv ≫ U.f (index j) := by
  have H (j : U.I₀) : ∃ f : Spec (.of (Polynomial (R ⊗[T] A j))) ⟶ Y,
      IsPullback
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A j →ₐ[T] R ⊗[T] A j).toRingHom)))
        f ((eU j).inv ≫ U.f j) q ∧
      f ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight : A j →ₐ[T] R ⊗[T] A j).toRingHom)) ≫
          (eU j).inv ≫ U.f j ∧
      f ≫ baseR = Spec.map (CommRingCat.ofHom
        (algebraMap R (Polynomial (R ⊗[T] A j)))) := by
    obtain ⟨_, _, _, HP⟩ := exists_scalar_polynomial_square T R (A j) (R ⊗[T] A j)
      (AlgEquiv.refl : R ⊗[T] A j ≃ₐ[R] R ⊗[T] A j)
    have HP' : IsPullback
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A j →ₐ[T] R ⊗[T] A j).toRingHom)))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] A j)))))
        (Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (A j)))))
        (Spec.map (CommRingCat.ofHom (algebraMap T R))) := HP
    obtain ⟨f, hf, hq, hb⟩ := scalar_chart_lift _ _ _ _ HP' q baseR base hY
      ((eU j).inv ≫ U.f j) (hU j)
    exact ⟨f, hf, hq, hb⟩
  choose f hf hq hb using H
  let κ (j : U.I₀) : Spec (.of (Polynomial (R ⊗[T] A j))) ⟶
      Spec (.of (Polynomial (A j))) :=
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Algebra.TensorProduct.includeRight : A j →ₐ[T] R ⊗[T] A j).toRingHom))
  let U₀ := Scheme.Cover.copy U U.I₀
    (fun j => Spec (.of (Polynomial (A j))))
    (fun j => (eU j).inv ≫ U.f j) (Equiv.refl _) (fun j => (eU j).symm) (fun _ => rfl)
  let V : Y.OpenCover.{u} := Scheme.Cover.copy (U₀.pullback₁ q) U.I₀
    (fun j => Spec (.of (Polynomial (R ⊗[T] A j)))) f
    (Equiv.refl _) (fun j => (hf j).flip.isoPullback)
    (fun j => (hf j).flip.isoPullback_hom_fst.symm)
  have hfinite : Finite V.I₀ := by
    change Finite U.I₀
    infer_instance
  have haffine : ∀ j, IsAffine (V.X j) := by
    intro j
    let j₀ : U.I₀ := j
    change IsAffine (Spec (.of (Polynomial (R ⊗[T] A j₀))))
    infer_instance
  let index : V.I₀ ≃ U.I₀ := Equiv.refl _
  let eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (R ⊗[T] A (index j)))) := by
    intro j
    let j₀ : U.I₀ := j
    change Spec (.of (Polynomial (R ⊗[T] A j₀))) ≅
      Spec (.of (Polynomial (R ⊗[T] A j₀)))
    exact Iso.refl _
  refine ⟨V, hfinite, haffine, index, eV, ?_, ?_, ?_⟩
  · intro j
    let j₀ : U.I₀ := j
    change IsPullback (𝟙 _ ≫ κ j₀) (f j₀) ((eU j₀).inv ≫ U.f j₀) q
    rw [Category.id_comp]
    exact hf j₀
  · intro j
    let j₀ : U.I₀ := j
    change f j₀ ≫ baseR = 𝟙 _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] A j₀))))
    rw [Category.id_comp]
    exact hb j₀
  · intro j
    let j₀ : U.I₀ := j
    change f j₀ ≫ q = 𝟙 _ ≫ κ j₀ ≫ (eU j₀).inv ≫ U.f j₀
    rw [Category.id_comp]
    exact hq j₀

/-- The prescribed field polynomial chart is the scalar chart of the
extended model when its two old projections and its structural map agree. -/
theorem append_scalar_field_chart
    {X Y Z A P PK B B₀ BK : Scheme.{u}}
    (q : Y ⟶ X) (n : Z ⟶ Y) (m : Z ⟶ X)
    (base : X ⟶ B₀) (baseR : Y ⟶ B) (baseK : Z ⟶ BK)
    (β : BK ⟶ B) (β₀ : BK ⟶ B₀)
    (hK : IsPullback n baseK baseR β)
    (h₀ : IsPullback m baseK base β₀) (hm : n ≫ q = m)
    (κR : P ⟶ A) (κK : PK ⟶ P) (κ₀ : PK ⟶ A)
    (hκ : κK ≫ κR = κ₀)
    (p : P ⟶ B) (pK : PK ⟶ BK)
    (hP : IsPullback κK pK p β)
    (j : A ⟶ X) (jR : P ⟶ Y) (jK : PK ⟶ Z)
    (hjR : jR ≫ q = κR ≫ j) (hjRb : jR ≫ baseR = p)
    (hjK : jK ≫ m = κ₀ ≫ j) (hjKb : jK ≫ baseK = pK) :
    IsPullback κK jK jR n ∧ jK ≫ n = κK ≫ jR := by
  obtain ⟨f, hf, hfn, hfb⟩ :=
    scalar_chart_lift κK pK p β hP n baseK baseR hK jR hjRb
  have hold : f ≫ m = κ₀ ≫ j := by
    calc
      f ≫ m = (f ≫ n) ≫ q :=
        (congrArg (f ≫ ·) hm.symm).trans (Category.assoc _ _ _).symm
      _ = (κK ≫ jR) ≫ q := congrArg (· ≫ q) hfn
      _ = κK ≫ (jR ≫ q) := Category.assoc _ _ _
      _ = κK ≫ (κR ≫ j) := congrArg (κK ≫ ·) hjR
      _ = (κK ≫ κR) ≫ j := (Category.assoc _ _ _).symm
      _ = κ₀ ≫ j := congrArg (· ≫ j) hκ
  have heq : f = jK := chart_lift_unique κ₀ pK β₀ m baseK base h₀ j
    f jK hold hjK hfb hjKb
  subst jK
  exact ⟨hf, hfn⟩

/-- The common finite affine cover retains the matching-chart projection,
the polynomial coordinate map and its field comparison. Smoothness gives
flat coordinate rings, so the comparison with the field chart is injective. -/
theorem exists_append_matching_coordinates {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    (hR : Function.Injective (algebraMap R K))
    {Y Z : Scheme.{u}} [Y.IsSeparated]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (baseK : Z ⟶ Spec (.of K)) (n : Z ⟶ Y)
    (hK : IsPullback n baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (W V : Y.OpenCover.{u}) [Finite W.I₀] [Finite V.I₀]
    [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (F : V.I₀ → Scheme.{u})
    (v : ∀ j, F j ⟶ V.X j) (jK : ∀ j, F j ⟶ Z)
    (hV : ∀ j, IsPullback (v j) (jK j) (V.f j) n) :
    let C := appendCommonCover W V
    Finite C.I₀ ∧ ∀ l : C.I₀,
      let P := pullback (C.f l) n
      let f := C.f l ≫ base
      let t := pullback.snd (C.f l) n ≫ baseK
      let q := pullback.fst (C.f l) n
      letI : IsAffine (C.X l) := inferInstance
      letI : IsAffine P := by
        let : IsAffineHom n := MorphismProperty.of_isPullback hK.flip inferInstance
        infer_instance
      let : Algebra R Γ(C.X l, ⊤) :=
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
      let : Algebra K Γ(P, ⊤) :=
        (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
      ∃ (a : Spec Γ(C.X l, ⊤) ⟶ W.X l.1)
        (kN : Spec Γ(C.X l, ⊤) ⟶ V.X l.2)
        (kF : Spec Γ(P, ⊤) ⟶ F l.2),
        IsOpenImmersion a ∧ IsOpenImmersion kN ∧
        a ≫ W.f l.1 = (C.X l).isoSpec.inv ≫ C.f l ∧
        kN ≫ V.f l.2 = (C.X l).isoSpec.inv ≫ C.f l ∧
        Spec.map q.appTop ≫ kN = kF ≫ v l.2 ∧
        kF ≫ jK l.2 = P.isoSpec.inv ≫ pullback.snd (C.f l) n ∧
        Module.Flat R Γ(C.X l, ⊤) ∧ Function.Injective q.appTop.hom ∧
        ∃ e : K ⊗[R] Γ(C.X l, ⊤) ≃ₐ[K] Γ(P, ⊤),
          (∀ k, e (k ⊗ₜ[R] (1 : Γ(C.X l, ⊤))) = algebraMap K Γ(P, ⊤) k) ∧
          (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
          ∀ k x, e (k ⊗ₜ[R] x) = algebraMap K Γ(P, ⊤) k * q.appTop.hom x := by
  let C := appendCommonCover W V
  change Finite C.I₀ ∧ ∀ l : C.I₀, _
  refine ⟨inferInstance, ?_⟩
  intro l
  let P := pullback (C.f l) n
  let f := C.f l ≫ base
  let t := pullback.snd (C.f l) n ≫ baseK
  let q := pullback.fst (C.f l) n
  let : IsAffineHom n := MorphismProperty.of_isPullback hK.flip inferInstance
  let : IsAffine P := inferInstance
  let : Smooth f := inferInstance
  let : Algebra R Γ(C.X l, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have H : IsPullback q t f
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    ((IsPullback.of_hasPullback (C.f l) n).flip.paste_horiz hK.flip).flip
  have hcoord := common_field_coordinates hR f t q H
  have hcomm : q ≫ appendCommonRight W V l ≫ V.f l.2 =
      pullback.snd (C.f l) n ≫ n := by
    exact (congrArg (q ≫ ·) (appendCommonRight_map W V l)).trans
      (pullback.condition (f := C.f l) (g := n))
  obtain ⟨k, hk, hj⟩ := lifted_chart_square q (pullback.snd (C.f l) n)
    (appendCommonRight W V l) (V.f l.2) n hcomm (v l.2) (jK l.2) (hV l.2)
  refine ⟨(C.X l).isoSpec.inv ≫ appendCommonLeft W V l,
    (C.X l).isoSpec.inv ≫ appendCommonRight W V l,
    P.isoSpec.inv ≫ k, inferInstance, inferInstance, ?_, ?_, ?_, ?_, hcoord⟩
  · exact (Category.assoc _ _ _).trans
      (congrArg ((C.X l).isoSpec.inv ≫ ·) (appendCommonLeft_map W V l))
  · exact (Category.assoc _ _ _).trans
      (congrArg ((C.X l).isoSpec.inv ≫ ·) (appendCommonRight_map W V l))
  · exact (coordinate_scalar_square q (appendCommonRight W V l) k (v l.2) hk).trans
      (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans (congrArg (P.isoSpec.inv ≫ ·) hj)

end SchubertGeometry
