import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionFactory
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionBase
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingRecursion
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionBoundaries
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeCartier
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordRawBoundary
import Mathlib.Data.List.Induction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Compatible splitting of a carried append model

The prefix functional normalizes the append operator on its prescribed
field fibre. Its earlier and last omitted-letter boundaries are preserved,
and scalar matching-line transport gives the next carried prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

open private normalizedOperator_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeCartier
open private raw_inserted_compatible from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordRawBoundary
open private closed_of_cartesian from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

namespace SchubertGeometry.RetainedCharacter

/-- Appending one letter preserves a splitting normalized by the canonical
matching section and compatible with every omitted-letter boundary. -/
theorem append_splits {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    {L : NextLetter M i} (step : AppendStep M L)
    (hM : PrefixSplits M) : PrefixSplits step.output.prefix := by
  rcases step with ⟨g, output, rawStep⟩
  intro κ κComm hκField C cField cκAlg p cChar cPerfect hp hp'
    coefficientMap X baseκ x hx B bD hB LF sF
  let tκAlg : Algebra output.T κ := (Spec.preimage coefficientMap).hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap output.T κ)) = coefficientMap :=
    Spec.map_preimage coefficientMap
  have hx' : IsPullback x baseκ output.cT.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap output.T κ))) := by
    rw [hmap]
    exact hx
  obtain ⟨f⟩ := @exists_append_prior_fibre.{u} K kField kClosed kZero G word M i L g
    output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg
  obtain ⟨ps⟩ := @appendPrior_from_induction.{u} K kField kClosed kZero G word M i L g
    output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg
    f C cField cκAlg p cChar hM hκField cPerfect hp hp'
  have hraw := @rawStep κ κComm tκAlg C cField cκAlg p cChar cPerfect
    (@AppendPriorFibre.nOpen.{u} K kField kClosed kZero G word M i L g output.T κ
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg f) (@AppendPriorFibre.nDir.{u} K kField kClosed kZero
        G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
        kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        output.T) κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg f) (@AppendPriorFibre.cPrior.{u} K kField kClosed
        kZero G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
        output.hMT).toRingHom) tκAlg f) (@AppendPriorFibre.hcPrior.{u} K kField kClosed kZero G word
        M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg f) (@AppendPriorSplitting.delta.{u} K kField kClosed
        kZero G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
        output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps) (@AppendPriorSplitting.hco.{u} K
        kField kClosed kZero G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
        output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps) (@AppendPriorSplitting.hn.{u} K
        kField kClosed kZero G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
        output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps) (@AppendPriorSplitting.hP.{u} K
        kField kClosed kZero G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
        output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps) (@AppendPriorSplitting.hr.{u} K
        kField kClosed kZero G word M i L g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
        output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps)
    ((@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L g output.T κ
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg f).pt.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C
        κ)))
    (@AppendPriorSplitting.Theta.{u} K kField kClosed kZero G word M i L g output.T κ
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps)
        (@AppendPriorSplitting.normalized.{u} K kField kClosed kZero G word M i L g output.T κ
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
        κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
        Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
        (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S
        output.T output.hMT).toRingHom) tκAlg f C cField cκAlg p cChar ps) hp hp' X baseκ x hx'
  obtain ⟨Theta, hnormal, hboundary⟩ :=
    @append_raw_boundaries.{u} K kField kClosed kZero G word M i L g output
      κ κComm tκAlg f C cField cκAlg p cChar cPerfect ps hp X baseκ x hx'
      B bD hB hraw
  exact @PrefixScalarModel.fibre_functional.{u,0} K kField kClosed kZero G
    (word ++ [i]) g.pre output C (@Field.toCommRing C cField) p cChar X
    (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) x
    (Fin (word ++ [i]).length) B Theta hnormal hboundary

private theorem word_from_seed {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} (seed : PrefixModel G []) (hseed : PrefixSplits seed)
    (word : List (@simpleRootIndex.{u} K kField kClosed kZero G)) :
    ∃ M : PrefixModel G word, PrefixSplits M := by
  refine List.reverseRecOn word ?_ ?_
  · exact ⟨seed, hseed⟩
  · intro prior i ih
    obtain ⟨M, hM⟩ := ih
    obtain ⟨step⟩ := @exists_append_step.{u} K kField kClosed kZero G prior M i
      (@PrefixModel.nextLetter.{u} K kField kClosed kZero G prior M i)
    exact ⟨step.output.prefix,
      @append_splits.{u} K kField kClosed kZero G prior M i
        (@PrefixModel.nextLetter.{u} K kField kClosed kZero G prior M i) step hM⟩


/-- A section-inserted splitting retains its raw functional and operator formula. -/
structure SectionSplitting (C : Type u) [cComm : CommRing C] (p : ℕ)
    [cChar : ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules) (s : Γ(L, ⊤)) where
  /-- The raw functional on the prescribed twisted module. -/
  Theta : @frobeniusRestriction.{u} C cComm p cChar X base L ⟶
    SheafOfModules.unit X.ringCatSheaf
  /-- The splitting defined by inserting the prescribed section. -/
  sigma : SchemeSplitting X p
  /-- The splitting's operator inserts the section into the same raw functional. -/
  operator_eq : sigma.toOperator =
    @ProjectiveCartier.twistedSectionOperator.{u} C cComm p cChar X base L Theta s

/-- A normalized prefix functional gives a splitting on every prescribed
field fibre, compatible with every carried omitted-letter model. -/
theorem PrefixModel.fibre_splitting {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (hM : PrefixSplits M) :
  ∀ (κ : Type u) [κComm : CommRing κ] (_hκField : IsField κ)
    (C : Type u) [_cField : Field C] [_cκAlg : Algebra C κ] (p : ℕ)
    [_cChar : ExpChar C p] [_cPerfect : PerfectRing C p]
    (_hp : Odd p) (_hp' : 1 < p)
    (coefficientMap : Spec (@CommRingCat.of κ κComm) ⟶ Spec (.of M.S))
    (X : Scheme.{u}) (baseκ : X ⟶ Spec (@CommRingCat.of κ κComm))
    (x : X ⟶ M.cG.pt.left)
    (_hx : IsPullback x baseκ M.cG.pt.hom coefficientMap)
    (B : Fin word.length → Over X)
    (bD : ∀ j, (B j).left ⟶ (M.boundaries j).left)
    (_hB : ∀ j, IsPullback (B j).hom (bD j) x (M.boundaries j).hom),
    let L := (Scheme.Modules.pullback x).obj
      (@matchingModule.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
          kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          M.S)
        M.N M.cG M.delta ((p - 1) / 2))
    let m := @pullSection.{u} X M.cG.pt.left x
      (@matchingModule.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
          kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          M.S)
        M.N M.cG M.delta ((p - 1) / 2))
      (@coefficientMatchingSection.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr
        ((p - 1) / 2))
    ∃ data : @SectionSplitting.{u} C (@Field.toCommRing C _cField) p _cChar X
        (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) L
        (m.app ⊤ (1 : Γ(X, ⊤))),
      ∀ j, data.sigma.IsCompatible (B j).hom.ker := by
  intro κ κComm hκField C cField cκAlg p cChar cPerfect hp hp'
    coefficientMap X baseκ x hx B bD hB L m
  obtain ⟨Theta, hnormal, hboundary⟩ :=
    @hM κ κComm hκField C cField cκAlg p cChar cPerfect hp hp'
      coefficientMap X baseκ x hx B bD hB
  let φ := @ProjectiveCartier.twistedSectionOperator.{u} C
    (@Field.toCommRing C cField) p cChar X
    (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) L Theta
    (m.app ⊤ (1 : Γ(X, ⊤)))
  have hφ : φ.onOpen ⊤ 1 = 1 :=
    (@ProjectiveCartier.twistedSectionOperator_one.{u} C
      (@Field.toCommRing C cField) p cChar X
      (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) L Theta
      (m.app ⊤ (1 : Γ(X, ⊤)))).trans hnormal
  let σ := @SchemeFrobeniusMap.toSplitting.{u} X p φ 1 hφ
  have hσ : σ.toOperator = φ := @normalizedOperator_eq.{u} X p φ hφ
  refine ⟨⟨Theta, σ, hσ⟩, ?_⟩
  intro j
  have hqc : QuasiCompact (B j).hom := by
    have : IsClosedImmersion (B j).hom :=
      @closed_of_cartesian.{u} (B j).left X
        (M.boundaries j).left M.cG.pt.left (B j).hom (bD j) x
        (M.boundaries j).hom (hB j) (M.hclosed j)
    infer_instance
  exact @raw_inserted_compatible.{u} C
    (@Field.toCommRing C cField) p cChar X (B j).left
    (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) L Theta
    (B j).hom hqc m σ hσ (hboundary j)


/-- Every initial segment of a word has a carried arithmetic model whose
canonical matching section normalizes a boundary-preserving functional. -/
theorem prefix_splits {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K)
    (word : List (@simpleRootIndex.{u} K kField kClosed kZero G)) :
    ∀ k (_hk : k ≤ word.length),
      ∃ M : PrefixModel G (word.take k), PrefixSplits M := by
  intro k _hk
  exact @word_from_seed.{u} K kField kClosed kZero G
    (@emptyPrefix.{u} K kField kClosed kZero G)
    (@emptyPrefix_splits.{u} K kField kClosed kZero G) (word.take k)

/-- A word has one carried model with its normalized functional and compatible
splittings on every prescribed field fibre of odd characteristic. -/
theorem word_splitting {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K)
    (word : List (@simpleRootIndex.{u} K kField kClosed kZero G)) :
    ∃ M : PrefixModel G word, PrefixSplits M ∧
  ∀ (κ : Type u) [κComm : CommRing κ] (_hκField : IsField κ)
    (C : Type u) [_cField : Field C] [_cκAlg : Algebra C κ] (p : ℕ)
    [_cChar : ExpChar C p] [_cPerfect : PerfectRing C p]
    (_hp : Odd p) (_hp' : 1 < p)
    (coefficientMap : Spec (@CommRingCat.of κ κComm) ⟶ Spec (.of M.S))
    (X : Scheme.{u}) (baseκ : X ⟶ Spec (@CommRingCat.of κ κComm))
    (x : X ⟶ M.cG.pt.left)
    (_hx : IsPullback x baseκ M.cG.pt.hom coefficientMap)
    (B : Fin word.length → Over X)
    (bD : ∀ j, (B j).left ⟶ (M.boundaries j).left)
    (_hB : ∀ j, IsPullback (B j).hom (bD j) x (M.boundaries j).hom),
    ∃ splitting : SchemeSplitting X p,
      ∀ j, splitting.IsCompatible (B j).hom.ker := by
  obtain ⟨M, hM⟩ : ∃ M : PrefixModel G word, PrefixSplits M :=
    Eq.mp (congrArg (fun v => ∃ M : PrefixModel G v, PrefixSplits M)
      (@List.take_length.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word))
      (@prefix_splits.{u} K kField kClosed kZero G word word.length (Nat.le_refl word.length))
  refine ⟨M, hM, ?_⟩
  intro κ κComm hκField C cField cκAlg p cChar cPerfect hp hp'
    coefficientMap X baseκ x hx B bD hB
  obtain ⟨data, hdata⟩ := @PrefixModel.fibre_splitting.{u}
    K kField kClosed kZero G word M hM κ κComm hκField C cField cκAlg
    p cChar cPerfect hp hp' coefficientMap X baseκ x hx B bD hB
  exact ⟨data.sigma, hdata⟩

end SchubertGeometry.RetainedCharacter
