import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordRawIdeals
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPolynomialCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedBoundary
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Raw Cartier preservation of the infinity section

The reciprocal chart operator preserves the zero-coordinate ideal before any
section is inserted or any normalization is chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private unitModule from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedOperatorMaps
open private indices line chart relativeBase sourceLine from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private polynomialCoframe commonChartData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierCharts
open private affineCoefficient affineCoefficient_eq spec_top_transport wordChartCoefficient_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierIdeals
open private raw_restrict framed_raw_preserves affine_range affine_coefficient_kernel
  raw_kernel_pushforward pushforward_of_openPullback range_kernel from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordRawIdeals
open private app_restrict from
  OrbitComplexity.FrobeniusSplitting.Splittings.AffineMorphisms
open private section_square from OrbitComplexity.FrobeniusSplitting.Compatible.CoverKernels
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private sectionWeight chartOpen from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private chart_openPullback from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedPullback
open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison
open private polynomialSource_value framedSectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPolynomialCoordinates
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private chartSection_top from
  OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalMonomials

private theorem inputWeight_one {X : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) : φ.inputWeight 1 = φ := by
  apply SchemeFrobeniusMap.ext
  intro U a
  rw [SchemeFrobeniusMap.inputWeight_apply, map_one, one_mul]

private def framedChart {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {A X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (k : A ⟶ X) [IsOpenImmersion k]
    (E : (Scheme.Modules.pullback k).obj L ≅ unitModule A)
    (H : (frobeniusRestriction C p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange) : SchemeFrobeniusMap A p :=
  (framedOpenOperator base L k.opensRange (coframeOverRange k L E) H).openPullback
    k.isoOpensRange.hom

private theorem framedChart_one {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {A X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (k : A ⟶ X) [IsOpenImmersion k]
    (E : (Scheme.Modules.pullback k).obj L ≅ unitModule A)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (m : unitModule X ⟶ L)
    (hm : ((pullbackObjUnitIso k).inv ≫ (Scheme.Modules.pullback k).map m) ≫ E.hom =
      globalSectionsSmul (unitModule A) 1)
    (Φ : SchemeFrobeniusMap X p)
    (hΦ : twistedSectionOperator base L Θ (m.app ⊤ (1 : Γ(X, ⊤))) = Φ) :
    framedChart base L k E (Θ.over k.opensRange) = Φ.openPullback k := by
  let U := k.opensRange
  let F := coframeOverRange k L E
  let c : Γ(X, U) := ((m.over U ≫ F.hom).val.app (op (Over.mk (𝟙 U)))).hom
    (1 : Γ(X, U))
  let φ := framedOpenOperator base L U F (Θ.over U)
  have hc : k.isoOpensRange.hom.appTop (U.topIso.inv c) = 1 :=
    coframeRange_section_coefficient k L m E 1 hm
  have hi := congrArg (fun q : SchemeFrobeniusMap U.toScheme p =>
    q.openPullback k.isoOpensRange.hom)
      (coframeInsertion_operator base L U F (m.over U) (Θ.over U))
  have hw := φ.openPullback_inputWeight k.isoOpensRange.hom (U.topIso.inv c)
  have hweight : (φ.openPullback k.isoOpensRange.hom).inputWeight
      (k.isoOpensRange.hom.appTop (U.topIso.inv c)) =
        φ.openPullback k.isoOpensRange.hom :=
    (congrArg (fun a : Γ(A, ⊤) => (φ.openPullback k.isoOpensRange.hom).inputWeight a)
      hc).trans (inputWeight_one _)
  have hg := congrArg (fun q : SchemeFrobeniusMap U.toScheme p =>
    q.openPullback k.isoOpensRange.hom)
      (twistedSectionOperator_onOpen base L Θ m U)
  have hΦU := congrArg (fun q : SchemeFrobeniusMap X p =>
    (q.restrict U).openPullback k.isoOpensRange.hom) hΦ
  have hchart : (Φ.restrict U).openPullback k.isoOpensRange.hom = Φ.openPullback k := by
    calc
      _ = (Φ.openPullback U.ι).openPullback k.isoOpensRange.hom :=
        congrArg (fun q : SchemeFrobeniusMap U.toScheme p =>
          q.openPullback k.isoOpensRange.hom) (Φ.openPullback_restrict U).symm
      _ = Φ.openPullback (k.isoOpensRange.hom ≫ U.ι) :=
        (Φ.openPullback_comp k.isoOpensRange.hom U.ι).symm
      _ = Φ.openPullback k := pullback_eq_of_hom_eq Φ k.isoOpensRange_hom_ι
  exact (hi.trans (hw.trans hweight)).symm.trans (hg.trans (hΦU.trans hchart))

private theorem reverse_power {A : Type u} [CommRing A] (d : ℕ) :
    ProjectiveLine.homogeneousReverse d (Polynomial.X ^ d : Polynomial A) = 1 := by
  classical
  simp [ProjectiveLine.homogeneousReverse, Polynomial.coeff_X_pow]

private theorem power_chart_one {A : Type u} [CommRing A] (d : ℕ) :
    RetainedCharacter.sectionChartPolynomial d (Polynomial.X ^ d : Polynomial A) 1 = 1 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simpa only [RetainedCharacter.sectionChartPolynomial, ite_eq_right h] using
    reverse_power (A := A) d

private def infinityGenerator (A : Type u) [CommRing A] (p : ℕ) :
    unitModule (line A) ⟶ sourceLine (A := A) (p := p) :=
  ProjectiveLine.projectivePolynomialSection A (p - 1) (Polynomial.X ^ (p - 1))
    (Polynomial.natDegree_X_pow_le _)

private theorem infinityGenerator_coordinate (A : Type u) [CommRing A] (p : ℕ) :
    ((pullbackObjUnitIso (chart A ⟨1⟩)).inv ≫
      (Scheme.Modules.pullback (chart A ⟨1⟩)).map (infinityGenerator A p)) ≫
        (polynomialCoframe A p ⟨1⟩).hom =
      globalSectionsSmul (unitModule (Spec (.of (Polynomial A)))) 1 := by
  have h := polynomialSource_value (A := A) p (Polynomial.X ^ (p - 1))
    (Polynomial.natDegree_X_pow_le _) ⟨1⟩
  change _ = globalSectionsSmul _
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (RetainedCharacter.sectionChartPolynomial (p - 1) (Polynomial.X ^ (p - 1)) 1)) at h
  exact h.trans (congrArg (globalSectionsSmul (unitModule (Spec (.of (Polynomial A)))))
    ((congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).inv (power_chart_one (p - 1))).trans
      (map_one _)))

private theorem module_value_eq {X : Scheme.{u}} {M N : X.Modules}
    (f g : M ⟶ N) (h : f = g) (U : X.Opens) (a : Γ(M, U)) :
    f.app U a = g.app U a := congrArg (fun q : M ⟶ N => q.app U a) h

private theorem infinityGenerator_weight (A : Type u) [CommRing A] (p : ℕ) :
    sectionWeight (p := p) (insertedInfinity (infinityGenerator A p)) ⟨1⟩ =
      (Polynomial.X ^ (p - 1) : Polynomial A) := by
  have hv := module_value_eq _ _
    (ProjectiveLine.projectivePolynomialSection_right A (p - 1)
      (Polynomial.X ^ (p - 1)) (Polynomial.natDegree_X_pow_le _))
        ⊤ (1 : Γ(line A, ⊤))
  have ht := chartSection_top A (⟨1⟩ : indices.{u})
    (ProjectiveLine.homogeneousReverse (p - 1) (Polynomial.X ^ (p - 1)))
  have hr := hv.trans ht
  have he : (Scheme.ΓSpecIso (.of (Polynomial A))).hom
      (((infinityGenerator A p ≫ pullback.snd (ProjectiveLine.leftRestriction A)
        (ProjectiveLine.twistedRestriction A (p - 1))).val.app (op ⊤)).hom
          (1 : Γ(line A, ⊤))) = 1 := by
    have h := congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom hr
    exact h.trans ((ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv_hom_id _).trans
      (reverse_power (A := A) (p - 1)))
  exact (insertedInfinity_right (infinityGenerator A p)).trans
    ((congrArg (fun q : Polynomial A => q * Polynomial.X ^ (p - 1)) he).trans (one_mul _))

private theorem trace_zero_ideal {K A : Type u} [Field K] {p : ℕ}
    [ExpChar K p] [PerfectRing K p] [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) :
    ∀ a ∈ RingHom.ker (Polynomial.evalRingHom (0 : A)),
      ((polynomialTraceOfOperator (K := K) ψ).weight (Polynomial.X ^ (p - 1))) a ∈
        RingHom.ker (Polynomial.evalRingHom (0 : A)) := by
  intro a ha
  change a.eval 0 = 0 at ha
  change Polynomial.eval 0
    (((polynomialTraceOfOperator (K := K) ψ).weight (Polynomial.X ^ (p - 1))) a) = 0
  have h := polynomialTrace_weight_eval_zero (K := K) ψ 1 a
  simpa only [one_mul, ha, FrobeniusLinearMap.map_zero] using h

private theorem relative_raw_reciprocal {K A : Type u} [Field K] {p : ℕ}
    [ExpChar K p] [PerfectRing K p] [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) :
    framedChart (relativeBase (K := K) (A := A)) (sourceLine (A := A) (p := p))
      (chart A ⟨1⟩) (polynomialCoframe A p ⟨1⟩)
      ((relativeTwistedCartierMap (K := K) ψ).over (chart A ⟨1⟩).opensRange) =
    (((polynomialTraceOfOperator (K := K) ψ).weight (Polynomial.X ^ (p - 1))).toSpec
      (expChar_pos K p)) := by
  let m := infinityGenerator A p
  let Φ := relativeCartierOperator (K := K) ψ (insertedInfinity m)
  let τ := ((polynomialTraceOfOperator (K := K) ψ).weight
    (Polynomial.X ^ (p - 1))).toSpec (expChar_pos K p)
  have hframe := framedChart_one (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (chart A ⟨1⟩) (polynomialCoframe A p ⟨1⟩)
      (relativeTwistedCartierMap (K := K) ψ) m (infinityGenerator_coordinate A p) Φ
        (twistedSectionOperator_relative (K := K) ψ m)
  have hchart := relativeCartierOperator_chart (K := K) ψ (insertedInfinity m) ⟨1⟩
  have hw := congrArg (fun Q : Polynomial A =>
    (((polynomialTraceOfOperator (K := K) ψ).weight Q).toSpec
      (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A ⟨1⟩).hom)
        (infinityGenerator_weight A p)
  have hτ : Φ.restrict (chartOpen A ⟨1⟩) =
      τ.pushforward (projectiveLinePolynomialIso A ⟨1⟩).hom := hchart.trans hw
  have hpull := chart_openPullback (chartOpen A ⟨1⟩)
    (projectiveLinePolynomialIso A ⟨1⟩) Φ τ hτ
  exact hframe.trans hpull

/-- The raw reciprocal word-chart coefficient preserves the zero-coordinate
ideal for every prior Frobenius-linear operator, without normalization. -/
theorem relativeWordChart_infinity {K A : Type u} [Field K] {p : ℕ}
    [ExpChar K p] [PerfectRing K p] [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (k : Spec (.of (Polynomial A)) ⟶ X) [IsOpenImmersion k]
    (E : (Scheme.Modules.pullback k).obj L ≅ unitModule (Spec (.of (Polynomial A)))) :
    ∀ a ∈ RingHom.ker (Polynomial.evalRingHom (0 : A)),
      wordChartCoefficient base L k E (relativeCartierWordChart ψ ⟨1⟩ base L k E) a ∈
        RingHom.ker (Polynomial.evalRingHom (0 : A)) := by
  have h := relativeCartierWordChart_coordinate ψ ⟨1⟩ base L k E
  change framedChart base L k E (relativeCartierWordChart ψ ⟨1⟩ base L k E) = _ at h
  have hraw := h.trans (relative_raw_reciprocal (K := K) ψ)
  apply affineCoefficient_eq _ _ hraw (RingHom.ker (Polynomial.evalRingHom (0 : A)))
  have he := spec_top_transport
    ((polynomialTraceOfOperator (K := K) ψ).weight (Polynomial.X ^ (p - 1)))
      (expChar_pos K p)
  intro a ha
  exact (congrArg (fun q : FrobeniusLinearMap (Polynomial A) p => q a) he).symm ▸
    trace_zero_ideal (K := K) ψ a ha

private theorem raw_line_on_image {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X Z : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (f : Z ⟶ X) {Idx : Type u} (U : Idx → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ∀ z : Z, ∃ i, f z ∈ U i)
    (hlocal : ∀ i (W : (U i).toScheme.affineOpens)
      (a : Γ(X, (U i).ι ''ᵁ W.1)), f.app ((U i).ι ''ᵁ W.1) a = 0 →
      ∀ e : Γ(L, (U i).ι ''ᵁ W.1),
        f.app ((U i).ι ''ᵁ W.1) (Θ.app ((U i).ι ''ᵁ W.1) (a • e)) = 0)
    (V : X.Opens) (a : Γ(X, V)) (ha : f.app V a = 0) (e : Γ(L, V)) :
    f.app V (Θ.app V (a • e)) = 0 := by
  apply Z.IsSheaf.section_ext
  intro z hz
  obtain ⟨i, hi⟩ := hcover z
  have : IsAffine (U i).toScheme := hU i
  let y : (U i).toScheme := ⟨f z, hi⟩
  have hy : y ∈ (U i).ι ⁻¹ᵁ V := hz
  obtain ⟨r, hr, hyr⟩ :=
    (isAffineOpen_top (U i).toScheme).exists_basicOpen_le ⟨y, hy⟩ (by trivial)
  let W : (U i).toScheme.affineOpens :=
    ⟨(U i).toScheme.basicOpen r, (isAffineOpen_top (U i).toScheme).basicOpen r⟩
  let T : X.Opens := (U i).ι ''ᵁ W.1
  have hT : T ≤ V := by
    rintro x ⟨t, ht, rfl⟩
    exact hr ht
  have hxT : f z ∈ T := ⟨y, hyr, rfl⟩
  let Q := f ⁻¹ᵁ T
  have hQ : Q ≤ f ⁻¹ᵁ V := fun _ hx => hT hx
  refine ⟨Q, hQ, hxT, ?_⟩
  let aT := X.presheaf.map (homOfLE hT).op a
  let eT := L.presheaf.map (homOfLE hT).op e
  have hin : f.app T aT = 0 := by
    rw [app_restrict f hT, ha, map_zero]
  have hout := hlocal i W aT hin eT
  calc
    Z.presheaf.map (homOfLE hQ).op (f.app V (Θ.app V (a • e))) =
        f.app T (X.presheaf.map (homOfLE hT).op (Θ.app V (a • e))) :=
      (app_restrict f hT _).symm
    _ = f.app T (Θ.app T (aT • eT)) :=
      congrArg (f.app T) (raw_restrict base L Θ hT a e).symm
    _ = 0 := hout
    _ = Z.presheaf.map (homOfLE hQ).op 0 := (map_zero _).symm

private theorem raw_kernel_on_image
    {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p] (hp : 0 < p)
    {X Z : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (f : Z ⟶ X) [QuasiCompact f] {Idx : Type u}
    (R S : Idx → Type u) [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (k : ∀ i, Spec (.of (R i)) ⟶ X) [∀ i, IsOpenImmersion (k i)]
    (g : ∀ i, R i →+* S i) (b : ∀ i, Spec (.of (S i)) ⟶ Z)
    (hcart : ∀ i, IsPullback (Spec.map (CommRingCat.ofHom (g i))) (b i) (k i) f)
    (E : ∀ i, (Scheme.Modules.pullback (k i)).obj L ≅ unitModule (Spec (.of (R i))))
    (hcover : ∀ z : Z, ∃ i y, k i y = f z)
    (hI : ∀ i, ∀ a ∈ RingHom.ker (g i),
      wordChartCoefficient base L (k i) (E i) (Θ.over (k i).opensRange) a ∈
        RingHom.ker (g i))
    (V : X.Opens) (a : Γ(X, V)) (ha : f.app V a = 0) (e : Γ(L, V)) :
    f.app V (Θ.app V (a • e)) = 0 := by
  let U : Idx → X.Opens := fun i => (k i).opensRange
  let F : ∀ i, L.over (U i) ≅ (unitModule X).over (U i) := fun i =>
    coframeOverRange (k i) L (E i)
  let φ : ∀ i, SchemeFrobeniusMap (U i).toScheme p := fun i =>
    framedOpenOperator base L (U i) (F i) (Θ.over (U i))
  let ψ : ∀ i, SchemeFrobeniusMap (Spec (.of (R i))) p := fun i =>
    (φ i).openPullback (k i).isoOpensRange.hom
  have hψ (i : Idx) : ∀ (W : (Spec (.of (R i))).Opens) (a : Γ(Spec (.of (R i)), W)),
      (Spec.map (CommRingCat.ofHom (g i))).app W a = 0 →
        (Spec.map (CommRingCat.ofHom (g i))).app W ((ψ i).onOpen W a) = 0 :=
    raw_kernel_of_top (ψ i) (Spec.map (CommRingCat.ofHom (g i))) hp
      (affine_coefficient_kernel (ψ i) (g i) (hI i))
  have hφ (i : Idx) : ∀ (W : (U i).toScheme.Opens) (a : Γ((U i).toScheme, W)),
      ((Spec.map (CommRingCat.ofHom (g i))) ≫ (k i).isoOpensRange.hom).app W a = 0 →
        ((Spec.map (CommRingCat.ofHom (g i))) ≫ (k i).isoOpensRange.hom).app W
          ((φ i).onOpen W a) = 0 := by
    have h := raw_kernel_pushforward (k i).isoOpensRange (ψ i)
      (Spec.map (CommRingCat.ofHom (g i))) (hψ i)
    have hEq := pushforward_of_openPullback (k i).isoOpensRange (φ i)
    exact hEq ▸ h
  have hK (i : Idx) :
      ((Spec.map (CommRingCat.ofHom (g i))) ≫ (k i).isoOpensRange.hom).ker =
        (f ∣_ U i).ker :=
    range_kernel (U i) (Spec.map (CommRingCat.ofHom (g i))) (b i) (k i) f
      (k i).isoOpensRange (k i).isoOpensRange_hom_ι (hcart i)
  apply raw_line_on_image base L Θ f U (fun i => affine_range (k i))
    (fun z => by
      obtain ⟨i, y, hy⟩ := hcover z
      exact ⟨i, ⟨y, hy⟩⟩) ?_ V a ha e
  intro i W a ha e
  have : QuasiCompact (f ∣_ U i) := inferInstance
  have hker := Scheme.ker_morphismRestrict_ideal f (U i) W
  have hin : a ∈ (f ∣_ U i).ker.ideal W := by
    rw [hker, Scheme.Hom.ker_apply]
    exact ha
  have hpres : ∀ a ∈ (f ∣_ U i).ker.ideal W, (φ i).onOpen W a ∈
      (f ∣_ U i).ker.ideal W := by
    intro a ha
    rw [← hK i, Scheme.Hom.ker_apply] at ha ⊢
    exact hφ i W a ha
  have hout := framed_raw_preserves base L (U i) (F i) (Θ.over (U i))
    W ((f ∣_ U i).ker.ideal W) hpres a hin e
  rw [hker, Scheme.Hom.ker_apply] at hout
  exact hout

private theorem chart_projection {D : Type*} [Category D] {A P B X Z : D}
    (j : A ⟶ P) (r : P ⟶ B) (a : A ⟶ B) (c : B ⟶ Z)
    (k : P ⟶ X) (q : X ⟶ Z) (hj : j ≫ r = a) (hk : k ≫ q = r ≫ c) :
    a ≫ c = (j ≫ k) ≫ q := by
  rw [Category.assoc, hk, ← Category.assoc, hj]

private theorem chart_section {D : Type*} [Category D] {A B P X Z : D}
    (t : B ⟶ A) (j : A ⟶ P) (s : B ⟶ P) (k : P ⟶ X)
    (c : B ⟶ Z) (δ : Z ⟶ X) (ht : t ≫ j = s) (hs : s ≫ k = c ≫ δ) :
    t ≫ (j ≫ k) = c ≫ δ := by rw [← Category.assoc, ht, hs]

/-- On the prescribed projective-line charts, the raw next Cartier map preserves
the kernel of the prescribed infinity section on every open subset. The same
projection and section may come from a scalar Cartesian model. -/
theorem wordCartier_raw_infinity
    {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
    {X Z : Scheme.{u}} (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (Θ : frobeniusRestriction K p base L ⟶ unitModule X)
    (q : X ⟶ Z) (δ : Z ⟶ X) [QuasiCompact δ] (hδ : δ ≫ q = 𝟙 Z)
    {Idx : Type u} (A : Idx → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (c : ∀ i, Spec (.of (A i)) ⟶ Z) [∀ i, IsOpenImmersion (c i)]
    (k : ∀ i, line (A i) ⟶ X) [∀ i, IsOpenImmersion (k i)]
    (hπ : ∀ i, k i ≫ q = GroupActions.projectiveToSpec (A i) indices ≫ c i)
    (hs : ∀ i, projectiveLineSection (A i) ⟨1⟩ ≫ k i = c i ≫ δ)
    (hcover : ∀ z : Z, ∃ i y, c i y = z)
    (E : ∀ i, (Scheme.Modules.pullback (chart (A i) ⟨1⟩ ≫ k i)).obj L ≅
      unitModule (Spec (.of (Polynomial (A i)))))
    (ψ : ∀ i, FrobeniusLinearMap (A i) p)
    (hΘ : ∀ i, Θ.over (chart (A i) ⟨1⟩ ≫ k i).opensRange =
      relativeCartierWordChart (ψ i) ⟨1⟩ base L (chart (A i) ⟨1⟩ ≫ k i) (E i))
    (V : X.Opens) (a : Γ(X, V)) (ha : δ.app V a = 0) (e : Γ(L, V)) :
    δ.app V (Θ.app V (a • e)) = 0 := by
  let j : ∀ i, Spec (.of (Polynomial (A i))) ⟶ X := fun i => chart (A i) ⟨1⟩ ≫ k i
  let g : ∀ i, Polynomial (A i) →+* A i := fun i => Polynomial.evalRingHom 0
  have hsect (i : Idx) : Spec.map (CommRingCat.ofHom (g i)) ≫ j i = c i ≫ δ :=
    chart_section (Spec.map (CommRingCat.ofHom (g i))) (chart (A i) ⟨1⟩)
      (projectiveLineSection (A i) ⟨1⟩) (k i) (c i) δ rfl (hs i)
  have hcart (i : Idx) : IsPullback (Spec.map (CommRingCat.ofHom (g i))) (c i) (j i) δ :=
    section_square (Spec.map (CommRingCat.ofHom (Polynomial.C : A i →+* Polynomial (A i))))
      q (c i) (j i) δ (Spec.map (CommRingCat.ofHom (g i)))
      (chart_projection (chart (A i) ⟨1⟩) (GroupActions.projectiveToSpec (A i) indices)
        _ (c i) (k i) q (projectiveLinePolynomialChart_base (A i) ⟨1⟩) (hπ i))
      hδ (hsect i)
  apply raw_kernel_on_image (expChar_pos K p) base L Θ δ
    (fun i => Polynomial (A i)) A j g c hcart E ?_ ?_ V a ha e
  · intro z
    obtain ⟨i, y, hy⟩ := hcover z
    refine ⟨i, (Spec.map (CommRingCat.ofHom (g i))) y, ?_⟩
    have h := congrArg (fun f : Spec (.of (A i)) ⟶ X => f y) (hsect i)
    exact h.trans (congrArg δ hy)
  · intro i
    exact wordChartCoefficient_eq base L (j i) (E i) _ _ (hΘ i)
      (RingHom.ker (g i)) (relativeWordChart_infinity (ψ i) base L (j i) (E i))

end SchubertGeometry.ProjectiveCartier
