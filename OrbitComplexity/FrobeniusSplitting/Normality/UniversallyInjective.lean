import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Injective morphisms over an algebraically closed field

An injective separated morphism whose source is locally of finite type over an
algebraically closed field is universally injective. Its diagonal has closed image
and contains every closed point of the fiber product; Jacobson density then gives
surjectivity of the diagonal.

## Main results

* `FrobeniusSplitting.universallyInjective_of_injective`: injectivity implies
  universal injectivity under the stated geometric hypotheses.
* `FrobeniusSplitting.purelyInseparable_of_specMap`: the field extension associated
  to a universally injective map of spectra is purely inseparable.
* `FrobeniusSplitting.quotientMap_universallyInjective`: preservation on quotient spectra.
* `FrobeniusSplitting.isField_of_universallyInjective`: a nonzero reduced algebra
  universally injective over a field is a field.

## Implementation notes

The fiber product need not be reduced. Closed points are represented by sections
over the algebraically closed field using Mathlib's scheme API.

## References

* The Stacks Project, Tag 01S4.
* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- Injectivity on closed points detects universal injectivity for separated morphisms
whose source is locally of finite type over an algebraically closed field. -/
theorem universallyInjective_of_closedPoints {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (morphism : X ⟶ Y) (base : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType (morphism ≫ base)] [IsSeparated morphism]
    (hinjective : Set.InjOn morphism (closedPoints X)) : UniversallyInjective morphism := by
  have := locallyOfFiniteType_of_comp morphism base
  let Z := pullback morphism morphism
  let structureMap : Z ⟶ Spec (.of K) := pullback.fst morphism morphism ≫ morphism ≫ base
  have : LocallyOfFiniteType structureMap := by dsimp [structureMap]; infer_instance
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace structureMap
  have hclosed : IsClosed (Set.range (pullback.diagonal morphism)) :=
    (pullback.diagonal morphism).isClosedEmbedding.isClosed_range
  have hpoints : closedPoints Z ⊆ Set.range (pullback.diagonal morphism) := by
    intro z hz
    let point := pointOfClosedPoint structureMap z hz
    let first := point ≫ pullback.fst morphism morphism
    let second := point ≫ pullback.snd morphism morphism
    have hfirst : first ≫ (morphism ≫ base) = 𝟙 _ := by
      simpa [first, structureMap, Category.assoc] using
        pointOfClosedPoint_comp structureMap z hz
    have hprojection : first ≫ morphism = second ≫ morphism := by
      simp only [first, second, Category.assoc, pullback.condition]
    have hsecond : second ≫ (morphism ≫ base) = 𝟙 _ := by
      rw [← Category.assoc, ← hprojection, Category.assoc, hfirst]
    have heq : first = second := by
      apply ext_of_apply_closedPoint_eq (morphism ≫ base) hfirst hsecond
      apply hinjective
        ((pointEquivClosedPoint (morphism ≫ base) ⟨first, hfirst⟩).2)
        ((pointEquivClosedPoint (morphism ≫ base) ⟨second, hsecond⟩).2)
      exact congrArg (fun f : Spec (.of K) ⟶ Y ↦ f (IsLocalRing.closedPoint K)) hprojection
    have hpoint : point = first ≫ pullback.diagonal morphism := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, first]
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, ← heq, second]
    refine ⟨first (IsLocalRing.closedPoint K), ?_⟩
    change (first ≫ pullback.diagonal morphism) (IsLocalRing.closedPoint K) = z
    rw [← hpoint]
    exact pointOfClosedPoint_apply structureMap z hz _
  have hrange : Set.range (pullback.diagonal morphism) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints (X := Z)]
    exact closure_minimal hpoints hclosed
  exact (UniversallyInjective.iff_diagonal morphism).2 ⟨Set.range_eq_univ.1 hrange⟩

/-- Universal injectivity on spectra of fields gives a purely inseparable extension. -/
theorem purelyInseparable_of_specMap {F E : Type u} [Field F] [Field E] [Algebra F E]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap F E)))] :
    IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff_subsingleton_emb, subsingleton_iff]
  intro first second
  apply AlgHom.toRingHom_injective
  have huniversal : UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap F E))) :=
    inferInstance
  have htest : ∀ (L : Type u) [Field L], Function.Injective
      (fun g : Spec (.of L) ⟶ Spec (.of E) ↦
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap F E))) :=
    ((tfae_universallyInjective
      (Spec.map (CommRingCat.ofHom (algebraMap F E)))).out 1 2).1 huniversal
  have hinjective := htest (AlgebraicClosure E)
  have hcomp :
      Spec.map (CommRingCat.ofHom first.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F E)) =
      Spec.map (CommRingCat.ofHom second.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact (first.commutes a).trans (second.commutes a).symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective (hinjective hcomp))

/-- The first map of a universally injective composite is universally injective. -/
theorem universallyInjective_of_comp {X Y Z : Scheme.{u}} (first : X ⟶ Y) (second : Y ⟶ Z)
    [UniversallyInjective (first ≫ second)] : UniversallyInjective first := by
  have huniversal : UniversallyInjective (first ≫ second) := inferInstance
  have htest : ∀ (L : Type u) [Field L], Function.Injective
      (fun g : Spec (.of L) ⟶ X ↦ g ≫ first ≫ second) :=
    ((tfae_universallyInjective (first ≫ second)).out 1 2).1 huniversal
  have hfirst : ∀ (L : Type u) [Field L], Function.Injective
      (fun g : Spec (.of L) ⟶ X ↦ g ≫ first) := by
    intro L _ a b hab
    apply htest L
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ second) hab
  exact ((tfae_universallyInjective first).out 1 2).2 hfirst

/-- A universally injective map on spectra remains universally injective after quotienting. -/
theorem quotientMap_universallyInjective {R S : Type u} [CommRing R] [CommRing S]
    (morphism : R →+* S) (ideal : Ideal S)
    [UniversallyInjective (Spec.map (CommRingCat.ofHom morphism))] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap ideal morphism le_rfl))) := by
  have hcomp :
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ideal morphism le_rfl)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal.comap morphism))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ideal)) ≫
        Spec.map (CommRingCat.ofHom morphism) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ideal))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : UniversallyInjective
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ideal)) ≫
        Spec.map (CommRingCat.ofHom morphism)) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  rw [← hcomp] at this
  exact universallyInjective_of_comp
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ideal morphism le_rfl)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal.comap morphism))))

/-- A nonzero reduced algebra universally injective over a field is a field. -/
theorem isField_of_universallyInjective {F S : Type u} [Field F] [CommRing S]
    [IsReduced S] [Nontrivial S] (morphism : F →+* S)
    [UniversallyInjective (Spec.map (CommRingCat.ofHom morphism))] : IsField S := by
  have hinjective : Function.Injective (PrimeSpectrum.comap morphism) :=
    (Spec.map (CommRingCat.ofHom morphism)).injective
  have : Subsingleton (PrimeSpectrum S) :=
    ⟨fun a b ↦ hinjective (Subsingleton.elim _ _)⟩
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.1 inferInstance

end FrobeniusSplitting
