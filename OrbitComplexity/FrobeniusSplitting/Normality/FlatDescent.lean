import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing

/-! # Normal local rings under flat surjective morphisms

Faithful flatness contracts principal denominator ideals. A normal domain therefore
descends along a faithfully flat algebra map. Local stalk maps of a flat morphism are
faithfully flat, so surjectivity descends normal local rings at every target point.
-/

noncomputable section
namespace FrobeniusSplitting
open CategoryTheory AlgebraicGeometry

private theorem normal_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsDomain S] [IsIntegrallyClosed S] :
    IsDomain R ∧ IsIntegrallyClosed R := by
  have hRS := FaithfulSMul.algebraMap_injective R S
  have : IsDomain R := hRS.isDomain _
  let F := FractionRing R
  let L := FractionRing S
  have : IsScalarTower R S L := inferInstance
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R S L]
    exact (IsFractionRing.injective S L).comp hRS
  let φ : F →ₐ[R] L := IsFractionRing.liftAlgHom (g := Algebra.ofId R L) hRL
  refine ⟨inferInstance, (isIntegrallyClosed_iff F).mpr ?_⟩
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  have hφ : IsIntegral S (φ (algebraMap R F a / algebraMap R F b)) :=
    (hx.map φ).tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hφ
  simp only [map_div₀, AlgHom.commutes] at hs
  have hbn : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbnL : algebraMap R L b ≠ 0 := fun h => hbn (hRL (by simpa using h))
  have hmul : algebraMap S L s * algebraMap R L b = algebraMap R L a :=
    (eq_div_iff hbnL).mp hs
  have heS : algebraMap R S a = algebraMap R S b * s := by
    apply IsFractionRing.injective S L
    rw [map_mul]
    change algebraMap R L a = algebraMap R L b * algebraMap S L s
    exact hmul.symm.trans (mul_comm _ _)
  have haS : algebraMap R S a ∈ (Ideal.span ({b} : Set R)).map (algebraMap R S) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, heS⟩
  have haR : a ∈ Ideal.span ({b} : Set R) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span ({b} : Set R))]
    exact haS
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp haR
  refine ⟨r, ?_⟩
  have hbnF : algebraMap R F b ≠ 0 :=
    fun h => hbn ((IsFractionRing.injective R F) (by simpa using h))
  apply (eq_div_iff hbnF).mpr
  rw [hr, map_mul, mul_comm]

universe u

/-- Normal local rings descend along a flat surjective morphism of schemes. -/
theorem stalks_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  have : IsDomain (X.presheaf.stalk x) := (hX x).1
  have : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact normal_of_faithfullyFlat (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)

end FrobeniusSplitting
