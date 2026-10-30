import OrbitComplexity.FrobeniusSplitting.Compatible.Local
import OrbitComplexity.FrobeniusSplitting.Compatible.Pushforward
import OrbitComplexity.FrobeniusSplitting.Compatible.SchemeComponents
import OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses
import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorCharts
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Batteries.Tactic.Lint

/-! # Compatibility of kernels on open charts

A splitting preserves a morphism kernel if its chart operators preserve the
kernels in the Cartesian chart diagrams. For a section of a bundle, the
Cartesian diagrams follow from the section equations and the open immersions.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace FrobeniusSplitting

private theorem iso_hom_apply_eq {A B : CommRingCat.{u}}
    (e f : A ≅ B) (h : e = f) (a : A) : e.hom a = f.hom a :=
  congrArg (fun i : A ≅ B => i.hom a) h

/-- The kernel on global sections of a spectrum map is the inverse image of
its ring kernel under the global-sections isomorphism. -/
theorem spec_kernel {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) :
    RingHom.ker (Spec.map (CommRingCat.ofHom g)).appTop.hom =
      (RingHom.ker g).comap (StructureSheaf.globalSectionsIso R).inv.hom := by
  let eR := (StructureSheaf.globalSectionsIso R).symm.commRingCatIsoToRingEquiv
  let eS := (StructureSheaf.globalSectionsIso S).symm.commRingCatIsoToRingEquiv
  have hR : Scheme.ΓSpecIso (.of R) = (StructureSheaf.globalSectionsIso R).symm := by
    apply Iso.ext_inv
    rfl
  have hS : Scheme.ΓSpecIso (.of S) = (StructureSheaf.globalSectionsIso S).symm := by
    apply Iso.ext_inv
    rfl
  ext a
  change (Spec.map (CommRingCat.ofHom g)).appTop a = 0 ↔ g (eR a) = 0
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)) a
  change (Scheme.ΓSpecIso (.of S)).hom ((Spec.map (CommRingCat.ofHom g)).appTop a) =
    g ((Scheme.ΓSpecIso (.of R)).hom a) at h
  have he : eS ((Spec.map (CommRingCat.ofHom g)).appTop a) = g (eR a) :=
    (iso_hom_apply_eq _ _ hS _).symm.trans
      (h.trans (congrArg g (iso_hom_apply_eq _ _ hR a)))
  rw [← he]
  exact eS.map_eq_zero_iff.symm

end FrobeniusSplitting

namespace FrobeniusSplitting.SchemeSplitting

private def chartRingEquiv {X : Scheme.{u}} (R : Type u) [CommRing R]
    (k : Spec (.of R) ⟶ X) [IsOpenImmersion k] :
    Γ(X, k ''ᵁ (⊤ : (Spec (.of R)).Opens)) ≃+* R :=
  (k.appIso ⊤).commRingCatIsoToRingEquiv.trans
    (StructureSheaf.globalSectionsIso R).symm.commRingCatIsoToRingEquiv

private theorem chart_kernel {X Z : Scheme.{u}} {R B : Type u}
    [CommRing R] [CommRing B] (f : Z ⟶ X) [QuasiCompact f]
    (β : R →+* B) (b : Spec (.of B) ⟶ Z) (k : Spec (.of R) ⟶ X)
    [IsOpenImmersion k] (hcart : IsPullback (Spec.map (CommRingCat.ofHom β)) b k f) :
    f.ker.ideal ⟨k ''ᵁ ⊤, (isAffineOpen_top (Spec (.of R))).image_of_isOpenImmersion k⟩ =
      (RingHom.ker β).comap (chartRingEquiv R k).toRingHom := by
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    f (Spec.map (CommRingCat.ofHom β)) b k hcart ⟨⊤, isAffineOpen_top (Spec (.of R))⟩
  have hspec : (Spec.map (CommRingCat.ofHom β)).ker.ideal
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ =
      (RingHom.ker β).comap (StructureSheaf.globalSectionsIso R).inv.hom := by
    rw [Scheme.Hom.ker_apply]
    change RingHom.ker (Spec.map (CommRingCat.ofHom β)).appTop.hom = _
    exact spec_kernel β
  rw [hspec] at h
  ext x
  have hx := congrArg
    (fun I : Ideal Γ(Spec (.of R), ⊤) => (k.appIso ⊤).hom x ∈ I) h
  change ((StructureSheaf.globalSectionsIso R).inv ((k.appIso ⊤).hom x) ∈
      RingHom.ker β) =
    ((k.appIso ⊤).inv ((k.appIso ⊤).hom x) ∈ f.ker.ideal
      ⟨k ''ᵁ ⊤, (isAffineOpen_top (Spec (.of R))).image_of_isOpenImmersion k⟩) at hx
  have hinv : (k.appIso ⊤).inv ((k.appIso ⊤).hom x) = x :=
    ConcreteCategory.congr_hom (k.appIso ⊤).hom_inv_id x
  rw [hinv] at hx
  change x ∈ f.ker.ideal
      ⟨k ''ᵁ ⊤, (isAffineOpen_top (Spec (.of R))).image_of_isOpenImmersion k⟩ ↔
    (StructureSheaf.globalSectionsIso R).inv ((k.appIso ⊤).hom x) ∈ RingHom.ker β
  exact Iff.of_eq hx.symm

/-- Minimal-prime relations among kernels on a spectrum atlas give compatible
scheme kernels by induction on their ranks. Rank-zero chart kernels are unit
ideals or minimal primes over zero; rank-one scheme kernels are compatible. -/
theorem isCompatible_ker_induction
    {X : Scheme.{u}} {p : ℕ} {κ : Type v} {ι : Type w}
    (splitting : SchemeSplitting X p) (hp : 1 < p)
    (R : κ → Type u) [∀ c, CommRing (R c)]
    (k : ∀ c, Spec (.of (R c)) ⟶ X) [∀ c, IsOpenImmersion (k c)]
    (hcover : ∀ x : X, ∃ c y, k c y = x)
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X) [∀ i, QuasiCompact (f i)]
    (B : ι → κ → Type u) [∀ i c, CommRing (B i c)]
    (β : ∀ i c, R c →+* B i c) (b : ∀ i c, Spec (.of (B i c)) ⟶ Y i)
    (hcart : ∀ i c, IsPullback (Spec.map (CommRingCat.ofHom (β i c))) (b i c) (k c) (f i))
    (rank : ι → ℕ)
    (hzero : ∀ i, rank i = 0 → ∀ c,
      RingHom.ker (β i c) = ⊤ ∨
        RingHom.ker (β i c) ∈ (⊥ : Ideal (R c)).minimalPrimes)
    (hone : ∀ i, rank i = 1 → splitting.IsCompatible (f i).ker)
    (hstep : ∀ i, 1 < rank i →
      ∃ a d, rank a < rank i ∧ rank d < rank i ∧
        ∀ c, RingHom.ker (β i c) = ⊤ ∨
          RingHom.ker (β i c) ∈
            (RingHom.ker (β a c) ⊔ RingHom.ker (β d c)).minimalPrimes) :
    ∀ i, splitting.IsCompatible (f i).ker := by
  let U : κ → X.affineOpens := fun c =>
    ⟨k c ''ᵁ ⊤, (isAffineOpen_top (Spec (.of (R c)))).image_of_isOpenImmersion (k c)⟩
  have hU : ⨆ c, (U c).1 = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨c, y, hy⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c, y, trivial, hy⟩
  have hbot : splitting.IsCompatible (⊥ : X.IdealSheafData) :=
    fun W => RingSplitting.compatible_bot (splitting.onOpen W)
  have hbase (i : ι) (hi : rank i ≤ 1) : splitting.IsCompatible (f i).ker := by
    by_cases hi0 : rank i = 0
    · refine hbot.minimalPrime hp U hU ?_
      intro c
      have h := minimalPrime_comap_sup (chartRingEquiv (R c) (k c)).toRingHom
        (chartRingEquiv (R c) (k c)).bijective
        (RingHom.ker (β i c)) (⊥ : Ideal (R c)) ⊥
        (by simpa only [sup_bot_eq] using hzero i hi0 c)
      have hzero_comap :
          (⊥ : Ideal (R c)).comap (chartRingEquiv (R c) (k c)).toRingHom = ⊥ :=
        Ideal.comap_bot_of_injective _ (chartRingEquiv (R c) (k c)).injective
      rw [hzero_comap, sup_bot_eq] at h
      have hi' := chart_kernel (f i) (β i c) (b i c) (k c) (hcart i c)
      rw [← hi'] at h
      exact h
    · exact hone i (by omega)
  refine isCompatible_induction splitting hp U hU (fun i => (f i).ker) rank hbase ?_
  intro i hi
  obtain ⟨a, d, ha, hd, hcomponent⟩ := hstep i hi
  refine ⟨a, d, ha, hd, ?_⟩
  intro c
  have h := minimalPrime_comap_sup (chartRingEquiv (R c) (k c)).toRingHom
    (chartRingEquiv (R c) (k c)).bijective
    (RingHom.ker (β i c)) (RingHom.ker (β a c)) (RingHom.ker (β d c)) (hcomponent c)
  have hi' := chart_kernel (f i) (β i c) (b i c) (k c) (hcart i c)
  have ha' := chart_kernel (f a) (β a c) (b a c) (k c) (hcart a c)
  have hd' := chart_kernel (f d) (β d c) (b d c) (k c) (hcart d c)
  rw [← hi', ← ha', ← hd'] at h
  exact h

private theorem compatible_comap_equiv
    {R S : Type*} [CommRing R] [CommRing S] {p : ℕ}
    (φ : RingSplitting R p) (ψ : RingSplitting S p) (e : R ≃+* S)
    (I : Ideal R) (he : ∀ x, e.symm (ψ x) = φ (e.symm x))
    (hI : ψ.IsCompatible (I.comap e.symm.toRingHom)) :
    φ.IsCompatible I := by
  intro x hx
  have h := hI (show e x ∈ I.comap e.symm.toRingHom by
    change e.symm (e x) ∈ I
    simpa only [e.symm_apply_apply] using hx)
  change e.symm (ψ (e x)) ∈ I at h
  simpa only [he, e.symm_apply_apply] using h

private theorem compatible_image
    {X Z A B : Scheme.{u}} {p : ℕ}
    (ambient : SchemeSplitting X p) (localSplitting : SchemeSplitting A p)
    (f : Z ⟶ X) [QuasiCompact f] (j : B ⟶ A)
    (b : B ⟶ Z) (k : A ⟶ X) [IsOpenImmersion k]
    (hcart : IsPullback j b k f)
    (hoperator : ambient.toOperator.openPullback k = localSplitting.toOperator)
    (hker : localSplitting.IsCompatible j.ker) (W : A.affineOpens) :
    (ambient.onOpen (k ''ᵁ W)).IsCompatible
      (f.ker.ideal ⟨k ''ᵁ W, W.2.image_of_isOpenImmersion k⟩) := by
  have hlocal := hker W
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f j b k hcart W] at hlocal
  apply compatible_comap_equiv (ambient.onOpen (k ''ᵁ W))
    (localSplitting.onOpen W) (k.appIso W).commRingCatIsoToRingEquiv
    (f.ker.ideal ⟨k ''ᵁ W, W.2.image_of_isOpenImmersion k⟩) _ hlocal
  intro x
  have h := ambient.toOperator.openPullback_appIso k W x
  rw [hoperator] at h
  exact h

/-- Compatibility on a nonempty open chart of an integral source implies
compatibility with its image kernel on the ambient scheme. -/
theorem isCompatible_ker_of_dense_chart
    {X Z A B : Scheme.{u}} {p : ℕ} [IsIntegral Z] [Nonempty B]
    (ambient : SchemeSplitting X p) (f : Z ⟶ X) [QuasiCompact f]
    (j : B ⟶ A) (b : B ⟶ Z) (k : A ⟶ X)
    [IsOpenImmersion k] [QuasiCompact k]
    (hcart : IsPullback j b k f)
    (localSplitting : SchemeSplitting A p)
    (hoperator : ambient.toOperator.openPullback k = localSplitting.toOperator)
    (hker : localSplitting.IsCompatible j.ker) :
    ambient.IsCompatible f.ker := by
  have : IsOpenImmersion b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcart
      (inferInstance : IsOpenImmersion k)
  have : IsDominant b :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace b b.isOpenEmbedding.isOpenMap⟩
  have : IsSchemeTheoreticallyDominant b :=
    IsSchemeTheoreticallyDominant.of_isDominant b
  have : QuasiCompact j :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcart.flip
      (inferInstance : QuasiCompact f)
  have heq : (j ≫ k).ker = f.ker := by
    rw [hcart.w, Scheme.Hom.ker_comp, b.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rw [← heq]
  intro U a ha
  rw [Scheme.Hom.ker_apply] at ha ⊢
  change j.app (k ⁻¹ᵁ U.1) (k.app U.1 a) = 0 at ha
  change j.app (k ⁻¹ᵁ U.1) (k.app U.1 (ambient.onOpen U.1 a)) = 0
  have hs := hker.ker_onOpen (k ⁻¹ᵁ U.1) (k.app U.1 a) ha
  have hn := ambient.toOperator.openPullback_natural k U.1 a
  rw [hoperator] at hn
  exact (congrArg (j.app (k ⁻¹ᵁ U.1)) hn).symm.trans hs

/-- Cartesian open charts detect compatibility with a morphism kernel. -/
theorem isCompatible_ker_of_cover
    {X Z : Scheme.{u}} {p : ℕ} (ambient : SchemeSplitting X p)
    (f : Z ⟶ X) [QuasiCompact f] (hp : 0 < p)
    {I : Type v} (A B : I → Scheme.{u})
    (k : ∀ i, A i ⟶ X) [∀ i, IsOpenImmersion (k i)]
    (b : ∀ i, B i ⟶ Z) (j : ∀ i, B i ⟶ A i)
    (hcart : ∀ i, IsPullback (j i) (b i) (k i) f)
    (hcover : ∀ x : X, ∃ i y, k i y = x)
    (localSplitting : ∀ i, SchemeSplitting (A i) p)
    (hoperator : ∀ i, ambient.toOperator.openPullback (k i) =
      (localSplitting i).toOperator)
    (hker : ∀ i, (localSplitting i).IsCompatible (j i).ker) :
    ambient.IsCompatible f.ker := by
  let U : (Σ i, (A i).affineOpens) → X.affineOpens :=
    fun z => ⟨k z.1 ''ᵁ z.2, z.2.2.image_of_isOpenImmersion (k z.1)⟩
  apply ambient.isCompatible_of_cover f.ker hp U
  · apply le_antisymm le_top
    intro x _
    obtain ⟨i, y, hy⟩ := hcover x
    obtain ⟨W, hW, hyW, _⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ (⊤ : (A i).Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨W, hW⟩⟩, y, hyW, hy⟩
  · rintro ⟨i, W⟩
    exact compatible_image ambient (localSplitting i) f (j i) (b i) (k i)
      (hcart i) (hoperator i) (hker i) W

private theorem section_square
    {C : Type*} [Category C] {A P X Z : C}
    (π : P ⟶ A) (q : X ⟶ Z) (c : A ⟶ Z) [Mono c]
    (k : P ⟶ X) [Mono k] (δ : Z ⟶ X) (t : A ⟶ P)
    (hπ : π ≫ c = k ≫ q) (hδ : δ ≫ q = 𝟙 Z)
    (ht : t ≫ k = c ≫ δ) : IsPullback t c k δ := by
  apply IsPullback.mk' ht
  · intro T a b _ h
    exact (cancel_mono c).mp h
  · intro T a b hab
    have ha : (a ≫ π) ≫ c = b := by
      calc
        (a ≫ π) ≫ c = a ≫ (k ≫ q) := by rw [Category.assoc, hπ]
        _ = b ≫ (δ ≫ q) := by rw [← Category.assoc, hab, Category.assoc]
        _ = b := by rw [hδ, Category.comp_id]
    refine ⟨a ≫ π, ?_, ha⟩
    apply (cancel_mono k).mp
    calc
      ((a ≫ π) ≫ t) ≫ k = (a ≫ π) ≫ (c ≫ δ) := by
        rw [Category.assoc, ht]
      _ = b ≫ δ := by rw [← Category.assoc, ha]
      _ = a ≫ k := hab.symm

/-- Local section equations and chart compatibility give compatibility of the
global section kernel. -/
theorem isCompatible_section_of_cover
    {X Z : Scheme.{u}} {p : ℕ} (ambient : SchemeSplitting X p)
    (q : X ⟶ Z) (δ : Z ⟶ X) [QuasiCompact δ]
    (hδ : δ ≫ q = 𝟙 Z) (hp : 0 < p)
    {I : Type v} (A P : I → Scheme.{u})
    (c : ∀ i, A i ⟶ Z) [∀ i, IsOpenImmersion (c i)]
    (k : ∀ i, P i ⟶ X) [∀ i, IsOpenImmersion (k i)]
    (π : ∀ i, P i ⟶ A i) (t : ∀ i, A i ⟶ P i)
    (hπ : ∀ i, π i ≫ c i = k i ≫ q)
    (ht : ∀ i, t i ≫ k i = c i ≫ δ)
    (hcover : ∀ x : X, ∃ i y, k i y = x)
    (localSplitting : ∀ i, SchemeSplitting (P i) p)
    (hoperator : ∀ i, ambient.toOperator.openPullback (k i) =
      (localSplitting i).toOperator)
    (hker : ∀ i, (localSplitting i).IsCompatible (t i).ker) :
    ambient.IsCompatible δ.ker :=
  isCompatible_ker_of_cover ambient δ hp P A k c t
    (fun i => section_square (π i) q (c i) (k i) δ (t i)
      (hπ i) hδ (ht i)) hcover localSplitting hoperator hker

end FrobeniusSplitting.SchemeSplitting
