import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorIdeals
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordRawIdeals
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Cartier kernels on retained affine charts

A Cartier morphism preserving the kernel of a boundary on every open preserves
the corresponding ring kernel on each Cartesian affine chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite FrobeniusSplitting

open private chartCoordinateIso retainedChartRange retainedCoordinateIso from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
open private range_kernel affine_range from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordRawIdeals

namespace SchubertGeometry.ProjectiveCartier

private def sectionsMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Γ(Y, ⊤) ⟶ Γ(X, ⊤) :=
  f.app ⊤

private def sectionsIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Γ(Y, ⊤) ≅ Γ(X, ⊤) :=
  Scheme.Γ.mapIso e.op

private theorem sectionsMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sectionsMap (f ≫ g) = sectionsMap g ≫ sectionsMap f := rfl

private theorem sectionsIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (sectionsIso e).hom = sectionsMap e.hom := rfl

private theorem kernel_comp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    RingHom.ker (f ≫ g).hom = (RingHom.ker g.hom).comap f.hom := by
  rw [RingHom.comap_ker]
  rfl

private theorem ideal_inverse {A B : CommRingCat.{u}} (e : A ≅ B)
    (I : Ideal A) (J : Ideal B) (h : I.comap e.inv.hom = J) :
    I = J.comap e.hom.hom := by
  rw [← h, Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.hom_inv_id]
  simp only [CommRingCat.hom_id, Ideal.comap_id]

private theorem ideal_three_isos {A B C D : CommRingCat.{u}}
    (e₀ : A ≅ B) (e₁ : A ≅ C) (e₂ : C ≅ D)
    (I : Ideal B) (J : Ideal A) (K : Ideal C) (L : Ideal D)
    (h₀ : J = I.comap e₀.hom.hom) (h₁ : J = K.comap e₁.hom.hom)
    (h₂ : K = L.comap e₂.hom.hom) :
    I.comap (e₀.symm ≪≫ e₁ ≪≫ e₂).inv.hom = L := by
  have hK : (I.comap e₀.hom.hom).comap e₁.inv.hom = K := by
    rw [← h₀, h₁, Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.inv_hom_id]
    simp only [CommRingCat.hom_id, Ideal.comap_id]
  have hL : K.comap e₂.inv.hom = L := by
    rw [h₂, Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.inv_hom_id]
    simp only [CommRingCat.hom_id, Ideal.comap_id]
  calc
    _ = ((I.comap e₀.hom.hom).comap e₁.inv.hom).comap e₂.inv.hom := by
      simp only [Iso.trans_inv, Iso.symm_inv, CommRingCat.hom_comp, Ideal.comap_comap,
          RingHom.comp_assoc]
    _ = L := by rw [hK, hL]

private theorem kernel_square {A B R S : CommRingCat.{u}}
    (f : A ⟶ B) (g : R ⟶ S) (eA : A ≅ R) (eB : B ≅ S)
    (h : f ≫ eB.hom = eA.hom ≫ g) :
    RingHom.ker f.hom = (RingHom.ker g.hom).comap eA.hom.hom := by
  ext a
  change f.hom a = 0 ↔ g.hom (eA.hom.hom a) = 0
  have hc : eB.hom.hom (f.hom a) = g.hom (eA.hom.hom a) :=
    congrArg (fun t : A ⟶ S => t.hom a) h
  rw [← hc]
  constructor
  · intro ha
    rw [ha, map_zero]
  · intro ha
    apply (ConcreteCategory.bijective_of_isIso eB.hom).1
    exact ha.trans (map_zero eB.hom.hom).symm

private theorem open_kernel_transport {X Z : Scheme.{u}} (f : Z ⟶ X)
    {U V : X.Opens} (h : U = V) :
    (RingHom.ker (f.app U).hom).comap (X.presheaf.map (eqToHom h).op).hom =
      RingHom.ker (f.app V).hom := by
  cases h
  simp

private theorem restricted_kernel {X Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact f] (U : X.Opens) [IsAffine U.toScheme] :
    RingHom.ker (sectionsMap (f ∣_ U)).hom =
      (RingHom.ker (f.app U).hom).comap U.topIso.hom.hom := by
  have h : RingHom.ker (sectionsMap (f ∣_ U)).hom =
      RingHom.ker (f.app (U.ι ''ᵁ ⊤)).hom := by
    have hs := Scheme.ker_morphismRestrict_ideal f U ⟨⊤, isAffineOpen_top _⟩
    simp only [Scheme.Hom.ker_apply] at hs
    exact hs
  have hi : (RingHom.ker (sectionsMap (f ∣_ U)).hom).comap U.topIso.inv.hom =
      RingHom.ker (f.app U).hom := by
    rw [h]
    exact open_kernel_transport f U.ι_image_top
  exact ideal_inverse U.topIso _ _ hi

private theorem kernel_iso_comp {P V Z : Scheme.{u}} (r : Z ⟶ P) (e : P ≅ V) :
    RingHom.ker (sectionsMap (r ≫ e.hom)).hom =
      (RingHom.ker (sectionsMap r).hom).comap (sectionsIso e).hom.hom := by
  rw [sectionsMap_comp, sectionsIso_hom]
  exact kernel_comp (sectionsMap e.hom) (sectionsMap r)

private theorem coordinate_kernel {A B : Type u} [CommRing A] [CommRing B]
    {X Z : Scheme.{u}} (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (f : Z ⟶ X) [QuasiCompact f] (g : A →+* B) (b : Spec (.of B) ⟶ Z)
    (hcart : IsPullback (Spec.map (CommRingCat.ofHom g)) b j f) :
    (RingHom.ker (f.app j.opensRange).hom).comap (chartCoordinateIso j).inv.hom =
      RingHom.ker g := by
  let U := j.opensRange
  let e := j.isoOpensRange
  let : IsAffine U.toScheme := affine_range j
  let r := Spec.map (CommRingCat.ofHom g)
  have hr := range_kernel U r b j f e (Scheme.Hom.isoOpensRange_hom_ι j) hcart
  have ht : RingHom.ker (sectionsMap (r ≫ e.hom)).hom =
      RingHom.ker (sectionsMap (f ∣_ U)).hom := by
    have hs := congrArg (fun I : U.toScheme.IdealSheafData =>
      I.ideal ⟨⊤, isAffineOpen_top _⟩) hr
    simp only [Scheme.Hom.ker_apply] at hs
    exact hs
  exact ideal_three_isos U.topIso (sectionsIso e) (Scheme.ΓSpecIso (.of A))
    (RingHom.ker (f.app U).hom) (RingHom.ker (sectionsMap (f ∣_ U)).hom)
    (RingHom.ker (sectionsMap r).hom) (RingHom.ker g)
    (restricted_kernel f U) (ht.symm.trans (kernel_iso_comp r e))
    (kernel_square (sectionsMap r) (CommRingCat.ofHom g) (Scheme.ΓSpecIso (.of A))
      (Scheme.ΓSpecIso (.of B)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)))

private theorem preserves_ideal_eq {A : Type u} [CommRing A] {p : ℕ}
    (φ : FrobeniusLinearMap A p) {I J : Ideal A} (h : I = J)
    (hI : ∀ a ∈ I, φ a ∈ I) : ∀ a ∈ J, φ a ∈ J := by
  cases h
  exact hI

variable {C R J : Type u} [CommRing C] [CommRing R]
    {p : ℕ} [ExpChar C p] [Category.{u} J] [Quiver.IsThin J]
    (N : J ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)

/-- Global preservation of a boundary kernel by a Cartier morphism implies
preservation of its affine ring kernel by each retained framed operator. -/
theorem retainedPrior_kernel (base : cN.pt.left ⟶ Spec (.of C))
    (L : cN.pt.left.Modules)
    (Θ : frobeniusRestriction C p base L ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (s : J) (frame : Γ(L, retainedChartRange N cN hcN s))
    {Z : Scheme.{u}} (f : Z ⟶ cN.pt.left) [QuasiCompact f]
    (A : Type u) [CommRing A] (g : N.obj s →+* A) (b : Spec (.of A) ⟶ Z)
    (hcart : IsPullback (Spec.map (CommRingCat.ofHom g)) b (cN.ι.app (op s)).left f)
    (hraw : ∀ (V : cN.pt.left.Opens) (a : Γ(cN.pt.left, V)), f.app V a = 0 →
      ∀ e : Γ(L, V), f.app V (Θ.app V (a • e)) = 0) :
    ∀ a ∈ RingHom.ker g,
      retainedTwistedPriorOperator N cN hcN base L Θ s frame a ∈ RingHom.ker g := by
  let I := RingHom.ker (f.app (retainedChartRange N cN hcN s)).hom
  have hI : ∀ a ∈ I, Θ.app (retainedChartRange N cN hcN s) (a • frame) ∈ I :=
    fun a ha => hraw _ a ha frame
  have hk : I.comap (retainedCoordinateIso N cN hcN s).inv.hom = RingHom.ker g :=
    @coordinate_kernel (N.obj s) A inferInstance inferInstance cN.pt.left Z
      (cN.ι.app (op s)).left ((retained_prior_charts N cN hcN).1 s)
      f inferInstance g b hcart
  exact preserves_ideal_eq (retainedTwistedPriorOperator N cN hcN base L Θ s frame) hk
    (retainedTwistedPrior_ideal N cN hcN base L Θ s frame I hI)

end SchubertGeometry.ProjectiveCartier
