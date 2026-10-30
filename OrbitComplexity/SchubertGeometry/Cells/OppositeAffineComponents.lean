import OrbitComplexity.SchubertGeometry.Cells.OppositeComponents
import OrbitComplexity.SchubertGeometry.Cells.RichardsonSchubert
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionKernels
import OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses
import Batteries.Tactic.Lint

/-! # Affine ideals of opposite Schubert components

An irreducible component remains a component on each open set it meets.
Its vanishing ideal is therefore a minimal prime of the intersection ideal
on every affine open set.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
open TopologicalSpace Opposite FrobeniusSplitting CategoryTheory.Limits

namespace SchubertGeometry

universe u v

private theorem maximal_irreducible_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (j : X → Y)
    (hj : IsOpenEmbedding j) (C T : Set Y) (hT : IsClosed T)
    (hC : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ T) C)
    (hne : (j ⁻¹' C).Nonempty) :
    Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ j ⁻¹' T) (j ⁻¹' C) := by
  obtain ⟨x, hx⟩ := hne
  have hmeet : (C ∩ Set.range j).Nonempty := ⟨j x, hx, x, rfl⟩
  refine ⟨⟨hC.1.1.preimage hj hmeet, Set.preimage_mono hC.1.2⟩, ?_⟩
  intro Z hZ hCZ
  have hirred : IsIrreducible (closure (j '' Z)) :=
    (hZ.1.image j hj.continuous.continuousOn).closure
  have hsubset : closure (j '' Z) ⊆ T := by
    apply closure_minimal _ hT
    rintro y ⟨z, hz, rfl⟩
    exact hZ.2 hz
  have hdense : C ⊆ closure (C ∩ Set.range j) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen
      hC.1.1.isPreirreducible hj.isOpen_range hmeet
  have himage : C ∩ Set.range j ⊆ j '' Z := by
    rintro y ⟨hy, z, rfl⟩
    exact ⟨z, hCZ hy, rfl⟩
  have hback : closure (j '' Z) ⊆ C :=
    hC.2 ⟨hirred, hsubset⟩ (hdense.trans (closure_mono himage))
  intro z hz
  exact hback (subset_closure ⟨z, hz, rfl⟩)

private theorem minimalPrime_of_zeroLocus {R : Type u} [CommRing R]
    (I P : Ideal R) (hP : P.IsPrime)
    (hmax : Maximal (fun Z : Set (PrimeSpectrum R) => IsIrreducible Z ∧
      Z ⊆ PrimeSpectrum.zeroLocus (I : Set R))
      (PrimeSpectrum.zeroLocus (P : Set R))) : P ∈ I.minimalPrimes := by
  have hIP : I ≤ P := by
    have h := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff P I).mp hmax.1.2
    simpa only [hP.isRadical.radical] using h
  refine ⟨⟨hP, hIP⟩, ?_⟩
  intro Q hQ hQP
  have hQirred : IsIrreducible (PrimeSpectrum.zeroLocus (Q : Set R)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical Q hQ.1.isRadical).mpr hQ.1
  have hback := hmax.2
    ⟨hQirred, PrimeSpectrum.zeroLocus_anti_mono_ideal hQ.2⟩
    (PrimeSpectrum.zeroLocus_anti_mono_ideal hQP)
  have h := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff Q P).mp hback
  simpa only [hQ.1.isRadical.radical] using h

private theorem affine_vanishingIdeal {X : Scheme.{u}} (C : Closeds X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U, hU⟩ =
      PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (C : Set X)) := rfl

private theorem vanishing_component_minimalPrime {R : Type u} [CommRing R]
    {X : Type v} [TopologicalSpace X] (j : PrimeSpectrum R → X)
    (hj : IsOpenEmbedding j) (A B C : Closeds X)
    (hC : Maximal (fun Z : Set X => IsIrreducible Z ∧
      Z ⊆ (A : Set X) ∩ (B : Set X)) (C : Set X)) :
    PrimeSpectrum.vanishingIdeal (j ⁻¹' (C : Set X)) = ⊤ ∨
      PrimeSpectrum.vanishingIdeal (j ⁻¹' (C : Set X)) ∈
        (PrimeSpectrum.vanishingIdeal (j ⁻¹' (A : Set X)) ⊔
          PrimeSpectrum.vanishingIdeal (j ⁻¹' (B : Set X))).minimalPrimes := by
  classical
  by_cases hne : (j ⁻¹' (C : Set X)).Nonempty
  · right
    have hmax := maximal_irreducible_preimage j
      hj (C : Set X) ((A : Set X) ∩ (B : Set X))
      (A.isClosed.inter B.isClosed) hC hne
    have hclosedC : IsClosed (j ⁻¹' (C : Set X)) := C.isClosed.preimage hj.continuous
    have hclosedA : IsClosed (j ⁻¹' (A : Set X)) := A.isClosed.preimage hj.continuous
    have hclosedB : IsClosed (j ⁻¹' (B : Set X)) := B.isClosed.preimage hj.continuous
    apply minimalPrime_of_zeroLocus _ _
      (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hmax.1.1)
    simpa only [PrimeSpectrum.zeroLocus_sup,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      hclosedC.closure_eq, hclosedA.closure_eq, hclosedB.closure_eq,
      Set.preimage_inter] using hmax
  · left
    rw [Set.not_nonempty_iff_eq_empty.mp hne, PrimeSpectrum.vanishingIdeal_empty]

private theorem affine_component_minimalPrime {X : Scheme.{u}}
    (A B C : Closeds X)
    (hC : Maximal (fun Z : Set X => IsIrreducible Z ∧
      Z ⊆ (A : Set X) ∩ (B : Set X)) (C : Set X))
    (U : X.Opens) (hU : IsAffineOpen U) :
    (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U, hU⟩ = ⊤ ∨
      (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U, hU⟩ ∈
        (((Scheme.IdealSheafData.vanishingIdeal A) ⊔
          (Scheme.IdealSheafData.vanishingIdeal B)).ideal ⟨U, hU⟩).minimalPrimes := by
  have h := vanishing_component_minimalPrime hU.fromSpec
    hU.fromSpec.isOpenEmbedding A B C hC
  have hsum := congrArg₂ (fun I J : Ideal Γ(X, U) => I ⊔ J)
    (affine_vanishingIdeal A U hU) (affine_vanishingIdeal B U hU)
  exact Eq.mpr (congrArg₂ (fun P I : Ideal Γ(X, U) =>
    P = ⊤ ∨ P ∈ I.minimalPrimes) (affine_vanishingIdeal C U hU) hsum) h

/-- The affine ideals of an opposite Schubert variety of codimension at
least two are either unit ideals or minimal primes over the sum of the
ideals of two opposite Schubert varieties of smaller codimension. -/
theorem exists_opposite_affine_components {K : Type u} [Field K]
    [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K) (w : G.weylGroup)
    (hw : 2 ≤ (weylCoxeterSystem G.rootBase).length w) :
    ∃ a b : G.weylGroup,
      (weylCoxeterSystem G.rootBase).length a <
        (weylCoxeterSystem G.rootBase).length w ∧
      (weylCoxeterSystem G.rootBase).length b <
        (weylCoxeterSystem G.rootBase).length w ∧
      ∀ U : (flagVariety G).scheme.affineOpens,
        (Scheme.IdealSheafData.vanishingIdeal (oppositeSchubertSupport G w)).ideal U = ⊤ ∨
          (Scheme.IdealSheafData.vanishingIdeal (oppositeSchubertSupport G w)).ideal U ∈
            (((Scheme.IdealSheafData.vanishingIdeal (oppositeSchubertSupport G a)) ⊔
              (Scheme.IdealSheafData.vanishingIdeal
                (oppositeSchubertSupport G b))).ideal U).minimalPrimes := by
  obtain ⟨a, b, _, ha, hb, hcomponent⟩ := exists_oppositeSchubert_components G w hw
  refine ⟨a, b, ha, hb, ?_⟩
  intro U
  have hsupport (z : G.weylGroup) :
      Set.range (oppositeSchubertInclusion G z).left =
        (oppositeSchubertSupport G z : Set (flagVariety G).scheme) :=
    oppositeSchubertInclusion_range G z
  rw [hsupport a, hsupport b, hsupport w] at hcomponent
  exact affine_component_minimalPrime (oppositeSchubertSupport G a)
    (oppositeSchubertSupport G b) (oppositeSchubertSupport G w) hcomponent U.1 U.2

private theorem closed_chart_kernel {K T : Type u} [kField : Field K]
    (X : GroupActions.Variety K) (Z : Closeds X.scheme)
    (U : T → X.scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    [hDiag : IsAffineHom (pullback.diagonal (terminal.from X.scheme))]
    (s : {s : Finset T // s.Nonempty}) :
    RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety Z).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion Z).left X.toSpec
      (fun t => (X.closedInclusion Z).left ⁻¹ᵁ U t) U id (fun _ => le_rfl)).app s).hom.toRingHom) =
    ((Scheme.IdealSheafData.vanishingIdeal Z).ideal
      ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩).comap
      ((intersectionOpens U).obj
        ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom.hom := by
  have hkernel : (X.closedInclusion Z).left.ker =
      Scheme.IdealSheafData.vanishingIdeal Z :=
    (Scheme.IdealSheafData.vanishingIdeal Z).ker_subschemeι
  have h := @intersectionCoordinateMap_ker.{u} X.scheme (X.closedSubvariety Z).scheme
    T K (@Field.toCommRing K kField) hDiag (X.closedInclusion Z).left
    (inferInstanceAs (QuasiCompact (X.closedInclusion Z).left)) X.toSpec U hU s
  exact h.trans (congrArg (fun I : X.scheme.IdealSheafData =>
    (I.ideal
      ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩).comap
      ((intersectionOpens U).obj
        ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom.hom) hkernel)

private theorem closed_chart_component {K T : Type u} [kField : Field K]
    (X : GroupActions.Variety K) (A B C : Closeds X.scheme)
    (hcomponent : ∀ V : X.scheme.affineOpens,
      (Scheme.IdealSheafData.vanishingIdeal C).ideal V = ⊤ ∨
      (Scheme.IdealSheafData.vanishingIdeal C).ideal V ∈
        (((Scheme.IdealSheafData.vanishingIdeal A) ⊔
          (Scheme.IdealSheafData.vanishingIdeal B)).ideal V).minimalPrimes)
    (U : T → X.scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (s : {s : Finset T // s.Nonempty}) :
    RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety C).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion C).left X.toSpec
      (fun t => (X.closedInclusion C).left ⁻¹ᵁ U t) U id
      (fun _ => le_rfl)).app s).hom.toRingHom) = ⊤ ∨
    RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety C).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion C).left X.toSpec
      (fun t => (X.closedInclusion C).left ⁻¹ᵁ U t) U id
      (fun _ => le_rfl)).app s).hom.toRingHom) ∈
      (RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety A).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion A).left X.toSpec
        (fun t => (X.closedInclusion A).left ⁻¹ᵁ U t) U id
        (fun _ => le_rfl)).app s).hom.toRingHom) ⊔
      RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety B).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion B).left X.toSpec
        (fun t => (X.closedInclusion B).left ⁻¹ᵁ U t) U id
        (fun _ => le_rfl)).app s).hom.toRingHom)).minimalPrimes := by
  let : IsSeparated (terminal.from X.scheme) := by
    rw [← terminal.comp_from X.toSpec]
    infer_instance
  let hDiag : IsAffineHom (pullback.diagonal (terminal.from X.scheme)) := by
    let : IsClosedImmersion (pullback.diagonal (terminal.from X.scheme)) :=
      IsSeparated.isClosedImmersion_diagonal (f := terminal.from X.scheme)
    infer_instance
  rw [@closed_chart_kernel.{u} K T kField X
        C U hU hDiag s,
    @closed_chart_kernel.{u} K T kField X
        A U hU hDiag s,
    @closed_chart_kernel.{u} K T kField X
        B U hU hDiag s]
  exact @minimalPrime_comap_sup.{u,u}
    Γ(((intersectionOpens U).obj
      ((intersectionIndexMap (id : T → T)).op.obj (op s))).toScheme, ⊤)
    Γ(X.scheme, (intersectionOpens U).obj
      ((intersectionIndexMap (id : T → T)).op.obj (op s)))
    (inferInstanceAs (CommSemiring Γ(((intersectionOpens U).obj
      ((intersectionIndexMap (id : T → T)).op.obj (op s))).toScheme, ⊤)))
    (inferInstanceAs (CommSemiring Γ(X.scheme, (intersectionOpens U).obj
      ((intersectionIndexMap (id : T → T)).op.obj (op s)))))
    ((intersectionOpens U).obj
      ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom.hom
    (ConcreteCategory.bijective_of_isIso (((intersectionOpens U).obj
      ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom))
    ((Scheme.IdealSheafData.vanishingIdeal C).ideal
      ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩)
    ((Scheme.IdealSheafData.vanishingIdeal A).ideal
      ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩)
    ((Scheme.IdealSheafData.vanishingIdeal B).ideal
      ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩)
    (hcomponent
      ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩)

/-- Two lower-rank opposite Schubert indices work on every affine-intersection
coordinate diagram: each larger-index kernel is the unit ideal or a minimal
prime over the sum of the two smaller-index kernels. -/
theorem exists_opposite_chart_components {K : Type u} [kField : Field K]
    [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (w : G.weylGroup)
    (hw : 2 ≤ (weylCoxeterSystem G.rootBase).length w) :
    ∃ a b : G.weylGroup,
      (weylCoxeterSystem G.rootBase).length a <
        (weylCoxeterSystem G.rootBase).length w ∧
      (weylCoxeterSystem G.rootBase).length b <
        (weylCoxeterSystem G.rootBase).length w ∧
      ∀ (T : Type u) (U : T → (flagVariety G).scheme.Opens)
        (_hU : ∀ t, IsAffineOpen (U t)) (s : {s : Finset T // s.Nonempty}),
        RingHom.ker
          (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (oppositeSchubertSupport G w)).scheme
            (flagVariety G).scheme T T K kField.toCommRing
            ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left
            (flagVariety G).toSpec
            (fun t => ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left ⁻¹ᵁ U t)
            U id (fun _ => le_rfl)).app s).hom.toRingHom) = ⊤ ∨
        RingHom.ker
          (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (oppositeSchubertSupport G w)).scheme
            (flagVariety G).scheme T T K kField.toCommRing
            ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left
            (flagVariety G).toSpec
            (fun t => ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left ⁻¹ᵁ U t)
            U id (fun _ => le_rfl)).app s).hom.toRingHom) ∈
          (RingHom.ker
            (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (oppositeSchubertSupport G a)).scheme
            (flagVariety G).scheme T T K kField.toCommRing
            ((flagVariety G).closedInclusion (oppositeSchubertSupport G a)).left
              (flagVariety G).toSpec
              (fun t => ((flagVariety G).closedInclusion (oppositeSchubertSupport G a)).left ⁻¹ᵁ U
                t)
              U id (fun _ => le_rfl)).app s).hom.toRingHom) ⊔
          RingHom.ker
            (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (oppositeSchubertSupport G b)).scheme
            (flagVariety G).scheme T T K kField.toCommRing
            ((flagVariety G).closedInclusion (oppositeSchubertSupport G b)).left
              (flagVariety G).toSpec
              (fun t => ((flagVariety G).closedInclusion (oppositeSchubertSupport G b)).left ⁻¹ᵁ U
                t)
              U id (fun _ => le_rfl)).app s).hom.toRingHom)).minimalPrimes := by
  obtain ⟨a, b, ha, hb, hcomponent⟩ := exists_opposite_affine_components G w hw
  refine ⟨a, b, ha, hb, ?_⟩
  intro T U hU s
  exact @closed_chart_component.{u} K T kField (flagVariety G)
    (oppositeSchubertSupport G a) (oppositeSchubertSupport G b)
    (oppositeSchubertSupport G w) hcomponent U hU s

private theorem whole_chart_component {K T : Type u} [kField : Field K]
    (X : GroupActions.Variety K) [hIntegral : IsIntegral X.scheme]
    (Z : Closeds X.scheme) (hZ : Z = ⊤)
    (U : T → X.scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (s : {s : Finset T // s.Nonempty}) :
    RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety Z).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion Z).left X.toSpec
      (fun t => (X.closedInclusion Z).left ⁻¹ᵁ U t) U id
      (fun _ => le_rfl)).app s).hom.toRingHom) = ⊤ ∨
    RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety Z).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion Z).left X.toSpec
      (fun t => (X.closedInclusion Z).left ⁻¹ᵁ U t) U id
      (fun _ => le_rfl)).app s).hom.toRingHom) ∈ (⊥ : Ideal _).minimalPrimes := by
  cases hZ
  let : IsSeparated (terminal.from X.scheme) := by
    rw [← terminal.comp_from X.toSpec]
    infer_instance
  let hDiag : IsAffineHom (pullback.diagonal (terminal.from X.scheme)) := by
    let : IsClosedImmersion (pullback.diagonal (terminal.from X.scheme)) :=
      IsSeparated.isClosedImmersion_diagonal (f := terminal.from X.scheme)
    infer_instance
  have hwhole : Maximal (fun W : Set X.scheme => IsIrreducible W ∧
      W ⊆ ((⊤ : Closeds X.scheme) : Set X.scheme) ∩
        ((⊤ : Closeds X.scheme) : Set X.scheme))
      ((⊤ : Closeds X.scheme) : Set X.scheme) := by
    refine ⟨⟨IrreducibleSpace.isIrreducible_univ X.scheme, ?_⟩, ?_⟩
    · intro x _
      exact ⟨trivial, trivial⟩
    · intro W _ _
      exact Set.subset_univ W
  have hzero : Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X.scheme) = ⊥ := by
    rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
  have hc := @closed_chart_component.{u} K T kField X ⊤ ⊤ ⊤
    (fun V => affine_component_minimalPrime (⊤ : Closeds X.scheme) ⊤ ⊤ hwhole V.1 V.2)
    U hU s
  have hk : RingHom.ker (((@intersectionCoordinateMap.{u} (X.closedSubvariety ⊤).scheme
      X.scheme T T K kField.toCommRing (X.closedInclusion ⊤).left X.toSpec
        (fun t => (X.closedInclusion ⊤).left ⁻¹ᵁ U t) U id
        (fun _ => le_rfl)).app s).hom.toRingHom) = (⊥ : Ideal _) := by
    rw [@closed_chart_kernel.{u} K T kField X ⊤ U hU hDiag s, hzero]
    exact Ideal.comap_bot_of_injective
      (((intersectionOpens U).obj
        ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom.hom)
      (ConcreteCategory.bijective_of_isIso (((intersectionOpens U).obj
        ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom)).1
  simpa only [hk, bot_sup_eq] using hc


/-- The identity opposite Schubert kernel is the unit ideal or a minimal
prime over zero on each affine-intersection coordinate chart. -/
theorem opposite_one_chart_component {K T : Type u} [kField : Field K]
    [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (w : G.weylGroup) (hw : w = 1)
    (U : T → (flagVariety G).scheme.Opens)
    (hU : ∀ t, IsAffineOpen (U t)) (s : {s : Finset T // s.Nonempty}) :
    RingHom.ker (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (oppositeSchubertSupport G w)).scheme
            (flagVariety G).scheme T T K kField.toCommRing
            ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left
      (flagVariety G).toSpec
      (fun t => ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left ⁻¹ᵁ U t)
      U id (fun _ => le_rfl)).app s).hom.toRingHom) = ⊤ ∨
    RingHom.ker (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (oppositeSchubertSupport G w)).scheme
            (flagVariety G).scheme T T K kField.toCommRing
            ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left
      (flagVariety G).toSpec
      (fun t => ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left ⁻¹ᵁ U t)
      U id (fun _ => le_rfl)).app s).hom.toRingHom) ∈ (⊥ : Ideal _).minimalPrimes := by
  cases hw
  exact @whole_chart_component.{u} K T kField (flagVariety G)
    (inferInstanceAs (IsIntegral (flagVariety G).scheme))
    (oppositeSchubertSupport G 1)
    (@oppositeSchubertSupport_one.{u} K kField kClosed kZero G) U hU s

end SchubertGeometry
