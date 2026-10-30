import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierIdeals
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorLocalization
import OrbitComplexity.FrobeniusSplitting.Splittings.AffineMorphisms
import OrbitComplexity.FrobeniusSplitting.Compatible.CoverKernels
import Mathlib.RingTheory.Localization.Ideal
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Restriction of raw Cartier ideal preservation

Frobenius-linear ideal preservation survives localization. On an affine scheme,
preservation of a morphism kernel on global sections therefore holds on every
open subset, and passes to arbitrary affine chart refinements.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private app_restrict from
  OrbitComplexity.FrobeniusSplitting.Splittings.AffineMorphisms
open private affineCoefficient from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierIdeals
open private unitModule from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedOperatorMaps

private theorem fraction_power {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    {p : ℕ} (hp : 0 < p) (a : R) (s : M) :
    IsLocalization.mk' S a s =
      IsLocalization.mk' S (a * (s : R) ^ (p - 1)) (s ^ p) := by
  apply IsLocalization.mk'_eq_iff_eq'.2
  change algebraMap R S (a * (s : R) ^ p) =
    algebraMap R S ((a * (s : R) ^ (p - 1)) * (s : R))
  congr 1
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]

private theorem localize_preserves {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    {p : ℕ} (φ : FrobeniusLinearMap R p) (hp : 0 < p)
    (I : Ideal R) (hI : ∀ a ∈ I, φ a ∈ I) :
    ∀ a ∈ I.map (algebraMap R S),
      φ.localize (S := S) M hp a ∈ I.map (algebraMap R S) := by
  intro x hx
  obtain ⟨⟨⟨a, ha⟩, s⟩, heq⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  have hx' : x = IsLocalization.mk' S a s :=
    (IsLocalization.mk'_eq_iff_eq_mul.2 heq.symm).symm
  rw [hx', fraction_power M hp, FrobeniusLinearMap.localize_mk']
  apply (IsLocalization.mem_map_algebraMap_iff M S).2
  exact ⟨⟨⟨φ (a * (s : R) ^ (p - 1)), hI _ (I.mul_mem_right _ ha)⟩, s⟩,
    IsLocalization.mk'_spec S _ _⟩

private theorem basic_kernel {X Z : Scheme.{u}} [IsAffine X] {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (g : Z ⟶ X) [QuasiCompact g]
    (hp : 0 < p)
    (hI : ∀ a ∈ RingHom.ker g.appTop.hom, φ.onOpen ⊤ a ∈ RingHom.ker g.appTop.hom)
    (r : Γ(X, ⊤)) (a : Γ(X, X.basicOpen r))
    (ha : g.app (X.basicOpen r) a = 0) :
    g.app (X.basicOpen r) (φ.onOpen (X.basicOpen r) a) = 0 := by
  have : IsLocalization.Away r Γ(X, X.basicOpen r) :=
    (isAffineOpen_top (X := X)).isLocalization_basicOpen r
  have hlocal := FrobeniusLinearMap.localize_eq (S := Γ(X, X.basicOpen r))
    (Submonoid.powers r) (φ.onOpen ⊤) hp (φ.onOpen (X.basicOpen r))
    (fun a => φ.restrict_comm le_top a)
  have hmap : (RingHom.ker g.appTop.hom).map (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r)) =
      RingHom.ker (g.app (X.basicOpen r)).hom := by
    have h := g.ker.map_ideal_basicOpen ⟨⊤, isAffineOpen_top X⟩ r
    simp only [Scheme.Hom.ker_apply] at h
    have hAlg : algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) =
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom := rfl
    exact (congrArg (fun t : Γ(X, ⊤) →+* Γ(X, X.basicOpen r) =>
      (RingHom.ker g.appTop.hom).map t) hAlg).trans h
  change a ∈ RingHom.ker (g.app (X.basicOpen r)).hom at ha
  change φ.onOpen (X.basicOpen r) a ∈ RingHom.ker (g.app (X.basicOpen r)).hom
  rw [← hmap] at ha ⊢
  rw [← hlocal]
  exact localize_preserves (Submonoid.powers r) (φ.onOpen ⊤) hp
    (RingHom.ker g.appTop.hom) hI a ha

/-- On an affine scheme, a raw Frobenius-linear operator preserving a morphism
kernel on global sections preserves that kernel on every open subset. -/
theorem raw_kernel_of_top {X Z : Scheme.{u}} [IsAffine X] {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (g : Z ⟶ X) [QuasiCompact g] (hp : 0 < p)
    (hI : ∀ a ∈ RingHom.ker g.appTop.hom, φ.onOpen ⊤ a ∈ RingHom.ker g.appTop.hom)
    (U : X.Opens) (a : Γ(X, U)) (ha : g.app U a = 0) :
    g.app U (φ.onOpen U a) = 0 := by
  apply Z.IsSheaf.section_ext
  intro z hz
  obtain ⟨r, hr, hzr⟩ := (isAffineOpen_top (X := X)).exists_basicOpen_le ⟨g z, hz⟩
    (by trivial)
  let W := g ⁻¹ᵁ X.basicOpen r
  have hW : W ≤ g ⁻¹ᵁ U := fun _ hx => hr hx
  refine ⟨W, hW, hzr, ?_⟩
  have hinput : g.app (X.basicOpen r) (X.presheaf.map (homOfLE hr).op a) = 0 := by
    rw [app_restrict g hr, ha, map_zero]
  calc
    Z.presheaf.map (homOfLE hW).op (g.app U (φ.onOpen U a)) =
        g.app (X.basicOpen r) (X.presheaf.map (homOfLE hr).op (φ.onOpen U a)) :=
      (app_restrict g hr _).symm
    _ = g.app (X.basicOpen r) (φ.onOpen (X.basicOpen r)
        (X.presheaf.map (homOfLE hr).op a)) :=
      congrArg (g.app (X.basicOpen r)) (φ.restrict_comm hr a).symm
    _ = 0 := basic_kernel φ g hp hI r _ hinput
    _ = Z.presheaf.map (homOfLE hW).op 0 := (map_zero _).symm


open private imageIn from
  OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators
open private twistedOverMap twistedOverMap_comp_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

private theorem raw_kernel_pushforward {A B X : Scheme.{u}} {p : ℕ}
    (e : A ≅ X) (φ : SchemeFrobeniusMap A p) (j : B ⟶ A)
    (hI : ∀ (V : A.Opens) (a : Γ(A, V)), j.app V a = 0 →
      j.app V (φ.onOpen V a) = 0) :
    ∀ (V : X.Opens) (a : Γ(X, V)), (j ≫ e.hom).app V a = 0 →
      (j ≫ e.hom).app V ((φ.pushforward e.hom).onOpen V a) = 0 := by
  intro V a ha
  change j.app (e.hom ⁻¹ᵁ V) (e.hom.app V a) = 0 at ha
  change j.app (e.hom ⁻¹ᵁ V) (e.hom.app V ((φ.pushforward e.hom).onOpen V a)) = 0
  rw [φ.pushforward_app]
  exact hI _ _ ha

private theorem pushforward_of_openPullback {A X : Scheme.{u}} {p : ℕ}
    (e : A ≅ X) (φ : SchemeFrobeniusMap X p) :
    (φ.openPullback e.hom).pushforward e.hom = φ :=
  (SchemeFrobeniusMap.operatorIsoEquiv e).apply_symm_apply φ

private theorem range_cartesian {A B X Z Y : Scheme.{u}}
    (j : B ⟶ A) (b : B ⟶ Z) (k : A ⟶ X) (f : Z ⟶ X)
    (e : A ≅ Y) (i : Y ⟶ X) (he : e.hom ≫ i = k)
    (hcart : IsPullback j b k f) :
    IsPullback (j ≫ e.hom) b i f := by
  apply hcart.of_iso (Iso.refl B) e (Iso.refl Z) (Iso.refl X)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem raw_restrict {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (e : Γ(L, U)) :
    Θ.app V ((X.presheaf.map (homOfLE h).op a) •
      (L.presheaf.map (homOfLE h).op e)) =
        X.presheaf.map (homOfLE h).op (Θ.app U (a • e)) := by
  have he : L.presheaf.map (homOfLE h).op e =
      (1 : Γ(X, V)) • L.presheaf.map (homOfLE h).op e := (one_smul _ _).symm
  have hφ := twistedFrameOperator_restrict base L Θ h e
    (L.presheaf.map (homOfLE h).op e) 1 he a
  change Θ.app V ((1 * X.presheaf.map (homOfLE h).op a) •
      L.presheaf.map (homOfLE h).op e) =
    X.presheaf.map (homOfLE h).op (Θ.app U (a • e)) at hφ
  simpa only [one_mul] using hφ

private theorem framed_raw_value {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (H : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U)
    (W : U.toScheme.Opens) (m : Γ(L, (imageIn U W).left)) :
    (H.val.app (op (imageIn U W))).hom m =
      (framedOpenOperator base L U E H).onOpen W
        ((E.hom.val.app (op (imageIn U W))).hom m) := by
  let V := imageIn U W
  have hE : (E.inv.val.app (op V)).hom ((E.hom.val.app (op V)).hom m) = m := by
    have h := congrArg
      (fun k : L.over U ⟶ L.over U => (k.val.app (op V)).hom m) E.hom_inv_id
    exact h
  have h₁ := openOperatorEquiv_apply C p base U
    (twistedOverMap base (unitModule X) L U E.inv ≫ H) W
    ((E.hom.val.app (op V)).hom m)
  have h₂ := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U
    E.inv H V ((E.hom.val.app (op V)).hom m)
  exact (h₁.trans (h₂.trans (congrArg (H.val.app (op V)).hom hE))).symm

private theorem framed_raw_preserves {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (H : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U)
    (W : U.toScheme.Opens) (I : Ideal Γ(X, (imageIn U W).left))
    (hI : ∀ a ∈ I, (framedOpenOperator base L U E H).onOpen W a ∈ I)
    (a : Γ(X, (imageIn U W).left)) (ha : a ∈ I) (m : Γ(L, (imageIn U W).left)) :
    (H.val.app (op (imageIn U W))).hom (a • m) ∈ I := by
  let : CommRing ((Sheaf.over X.ringCatSheaf U).obj.obj (op (imageIn U W))) :=
    inferInstanceAs (CommRing Γ(X, (imageIn U W).left))
  rw [framed_raw_value base L U E H W]
  apply hI
  let c : Γ(X, (imageIn U W).left) :=
    (E.hom.val.app (op (imageIn U W))).hom m
  have hmul : (E.hom.val.app (op (imageIn U W))).hom (a • m) =
      a * c := by
    have h := (E.hom.val.app (op (imageIn U W))).hom.map_smul a m
    exact h
  exact hmul.symm ▸ I.mul_mem_right c ha

private theorem affine_coefficient_kernel {R S : Type u} [CommRing R] [CommRing S]
    {p : ℕ} (φ : SchemeFrobeniusMap (Spec (.of R)) p) (g : R →+* S)
    (hI : ∀ a ∈ RingHom.ker g, affineCoefficient φ a ∈ RingHom.ker g) :
    ∀ a ∈ RingHom.ker (Spec.map (CommRingCat.ofHom g)).appTop.hom,
      φ.onOpen ⊤ a ∈ RingHom.ker (Spec.map (CommRingCat.ofHom g)).appTop.hom := by
  let e := (StructureSheaf.globalSectionsIso R).symm.commRingCatIsoToRingEquiv
  intro a ha
  rw [spec_kernel] at ha ⊢
  change e (φ.onOpen ⊤ a) ∈ RingHom.ker g
  have he : affineCoefficient φ (e a) = e (φ.onOpen ⊤ a) := by
    change e (φ.onOpen ⊤ (e.symm (e a))) = e (φ.onOpen ⊤ a)
    exact congrArg (fun b : Γ(Spec (.of R), ⊤) => e (φ.onOpen ⊤ b))
      (e.symm_apply_apply a)
  exact he ▸ hI _ ha

private theorem range_kernel {A B X Z : Scheme.{u}} (U : X.Opens)
    (j : B ⟶ A) (b : B ⟶ Z) (k : A ⟶ X) (f : Z ⟶ X)
    (e : A ≅ U.toScheme) (he : e.hom ≫ U.ι = k)
    (hcart : IsPullback j b k f) :
    (j ≫ e.hom).ker = (f ∣_ U).ker := by
  have h := range_cartesian j b k f e U.ι he hcart
  let E : B ≅ (f ⁻¹ᵁ U).toScheme :=
    h.isoIsPullback U.toScheme Z (isPullback_morphismRestrict f U)
  have hE : E.hom ≫ (f ∣_ U) = j ≫ e.hom :=
    h.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict f U)
  exact (congrArg (fun t : B ⟶ U.toScheme => t.ker) hE).symm.trans
    (Scheme.Hom.ker_comp_of_isIso E.hom (f ∣_ U))

private theorem affine_range {R : Type u} [CommRing R] {X : Scheme.{u}}
    (k : Spec (.of R) ⟶ X) [IsOpenImmersion k] : IsAffineOpen k.opensRange := by
  have h : k ''ᵁ ⊤ = k.opensRange := by
    apply TopologicalSpace.Opens.ext
    change k '' (Set.univ : Set (Spec (.of R))) = Set.range k
    exact Set.image_univ
  rw [← h]
  exact (isAffineOpen_top (Spec (.of R))).image_of_isOpenImmersion k

private theorem raw_line_of_cover {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X Z : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (f : Z ⟶ X) {Idx : Type u} (U : Idx → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hlocal : ∀ i (W : (U i).toScheme.affineOpens)
      (a : Γ(X, (U i).ι ''ᵁ W.1)), f.app ((U i).ι ''ᵁ W.1) a = 0 →
      ∀ e : Γ(L, (U i).ι ''ᵁ W.1),
        f.app ((U i).ι ''ᵁ W.1) (Θ.app ((U i).ι ''ᵁ W.1) (a • e)) = 0)
    (V : X.Opens) (a : Γ(X, V)) (ha : f.app V a = 0) (e : Γ(L, V)) :
    f.app V (Θ.app V (a • e)) = 0 := by
  apply Z.IsSheaf.section_ext
  intro z hz
  obtain ⟨i, hi⟩ := hcover (f z)
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

/-- Preservation by the affine coefficient operators implies raw
line-valued preservation of the boundary kernel on every open subset.
The Cartesian affine charts and their coframes supply the identifications. -/
theorem raw_cartier_kernel_of_charts
    {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p] (hp : 0 < p)
    {X Z : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (f : Z ⟶ X) [QuasiCompact f] {Idx : Type u}
    (R S : Idx → Type u) [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (k : ∀ i, Spec (.of (R i)) ⟶ X) [∀ i, IsOpenImmersion (k i)]
    (g : ∀ i, R i →+* S i) (b : ∀ i, Spec (.of (S i)) ⟶ Z)
    (hcart : ∀ i, IsPullback (Spec.map (CommRingCat.ofHom (g i))) (b i) (k i) f)
    (E : ∀ i, (Scheme.Modules.pullback (k i)).obj L ≅ unitModule (Spec (.of (R i))))
    (hcover : ∀ x : X, ∃ i y, k i y = x)
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
  apply raw_line_of_cover base L Θ f U (fun i => affine_range (k i))
    (fun x => by
      obtain ⟨i, y, hy⟩ := hcover x
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

end SchubertGeometry.ProjectiveCartier
