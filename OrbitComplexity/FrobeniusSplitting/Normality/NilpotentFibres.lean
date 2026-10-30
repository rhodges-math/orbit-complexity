import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.Polynomial.Basic

/-! # Nilpotent affine-line fibres

A nilpotent affine-line coordinate determines every field-valued point over its base.
A section then makes each geometric fibre nonempty, so its underlying space is connected.
-/

noncomputable section
namespace FrobeniusSplitting
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u

private theorem field_coordinate_zero {R L : Type u} [CommRing R] [Field L]
    {I : Scheme.{u}} (c : I ⟶ Spec (CommRingCat.of R[X]))
    (hnil : IsNilpotent
      (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X)))
    (p : Spec (CommRingCat.of L) ⟶ I)
    (φ : CommRingCat.of R[X] ⟶ CommRingCat.of L)
    (hφ : Spec.map φ = p ≫ c) : φ.hom Polynomial.X = 0 := by
  have hn := (hnil.map p.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
  have he : (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      ((Spec.map φ).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X)) =
      φ.hom Polynomial.X := by
    have h := congrArg (fun a : Γ(Spec (CommRingCat.of R[X]), ⊤) ⟶ CommRingCat.of L =>
      a ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X))
      (Scheme.ΓSpecIso_naturality φ)
    change (Scheme.ΓSpecIso (CommRingCat.of L)).hom
        ((Spec.map φ).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X)) =
      φ.hom (((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv ≫
        (Scheme.ΓSpecIso (CommRingCat.of R[X])).hom) Polynomial.X) at h
    rw [Iso.inv_hom_id] at h
    exact h
  rw [hφ] at he
  change IsNilpotent ((Scheme.ΓSpecIso (CommRingCat.of L)).hom
    ((p ≫ c).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X))) at hn
  rw [he] at hn
  exact isNilpotent_iff_eq_zero.mp hn

private theorem nilpotent_line_injective {R : Type u} [CommRing R] {I : Scheme.{u}}
    (b : I ⟶ Spec (CommRingCat.of R))
    (c : Over.mk b ⟶ Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))))
    [IsClosedImmersion c.left]
    (hnil : IsNilpotent
      (c.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X))) :
    UniversallyInjective b := by
  apply ((tfae_universallyInjective b).out 1 2).mpr
  intro L _ p q hpq
  apply (cancel_mono c.left).mp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (p ≫ c.left)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (q ≫ c.left)
  have hc : c.left ≫ Spec.map
      (CommRingCat.ofHom (Polynomial.C : R →+* R[X])) = b := c.w
  have hcoef : (CommRingCat.ofHom (Polynomial.C : R →+* R[X])) ≫ φ =
      (CommRingCat.ofHom (Polynomial.C : R →+* R[X])) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Category.assoc, hc]
    exact hpq
  have hx : φ.hom Polynomial.X = ψ.hom Polynomial.X :=
    (field_coordinate_zero c.left hnil p φ hφ).trans
      (field_coordinate_zero c.left hnil q ψ hψ).symm
  have he : φ = ψ := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext _ hx
    intro a
    exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of L => k a) hcoef
  exact hφ.symm.trans ((congrArg Spec.map he).trans hψ)

private theorem geometric_of_injective_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyInjective f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ y
  let P : Scheme.{u} := pullback f y
  have hinj : Function.Injective (pullback.snd f y) :=
    UniversallyInjective.universally_injective (f := f)
      (pullback.fst f y) y (pullback.snd f y) (IsPullback.of_hasPullback f y).flip
  let : Subsingleton P := ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  let τ : Spec (CommRingCat.of L) ⟶ P :=
    pullback.lift (y ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  let : Nonempty P := ⟨τ (IsLocalRing.closedPoint L)⟩
  change ConnectedSpace P
  exact connectedSpace_iff_univ.mpr
    ⟨Set.univ_nonempty, Set.subsingleton_univ.isPreconnected⟩

/-- A nilpotent affine-line coordinate and a base section give connected geometric fibres. -/
theorem geomConnected_of_nilpotent_chart {R : Type u} [CommRing R] {I : Scheme.{u}}
    (b : I ⟶ Spec (CommRingCat.of R))
    (c : Over.mk b ⟶ Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))))
    [IsClosedImmersion c.left]
    (hnil : ∃ N : ℕ, 0 < N ∧
      (c.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv Polynomial.X)) ^ N = 0)
    (hsection : ∃ σ : Spec (CommRingCat.of R) ⟶ I, σ ≫ b = 𝟙 _) :
    GeometricallyConnected b := by
  obtain ⟨N, _, hN⟩ := hnil
  let : UniversallyInjective b := nilpotent_line_injective b c ⟨N, hN⟩
  obtain ⟨σ, hσ⟩ := hsection
  exact geometric_of_injective_section b σ hσ

end FrobeniusSplitting
