import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingRecursion
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordPriorBoundary
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.PriorKernelCharts
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Raw Cartier preservation for the carried append boundaries

The Cartier functional on the append fibre preserves its
omitted-letter boundaries. Earlier boundaries use the carried prior kernels;
the last boundary is the Cartesian infinity section of the same append.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private AppendChartData AppendChartData.N AppendChartData.I AppendChartData.sel
  AppendChartContext AppendChartContext.D AppendChartContext.eP AppendChartContext.cD
  AppendChartContext.base AppendChartStage AppendChartStage.q from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
open private fieldRings scalarCoefficients fieldPolynomials fieldNodeBase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordSplitting
open private chartRaw polynomialLeg unitModule from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private nodePrior from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings

namespace SchubertGeometry.RetainedCharacter

private theorem inverse_node_projection {D : Type v} [Category D]
    {U V A X Y : D} (e : U ≅ V) (l : U ⟶ X) (q : X ⟶ Y)
    (π : U ⟶ A) (p : V ⟶ A) (c : A ⟶ Y)
    (hl : l ≫ q = π ≫ c) (hπ : π = e.hom ≫ p) :
    (e.inv ≫ l) ≫ q = p ≫ c := by
  rw [Category.assoc, hl, hπ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem pullback_right_eq {D : Type v} [Category D]
    {P X Y Z : D} {f : P ⟶ X} {z : P ⟶ Y} {q q' : X ⟶ Z} {d : Y ⟶ Z}
    (hq : q = q') (h : IsPullback f z q d) : IsPullback f z q' d := by
  cases hq
  exact h

private theorem projection_factor {D : Type v} [Category D]
    {X Y Z W P Q A B : D}
    (x : X ⟶ Y) (q : Y ⟶ Z) (a : Z ⟶ W) (c : W ⟶ Q)
    (π : X ⟶ P) (b : P ⟶ Q) (r : Q ⟶ A) (s : A ⟶ B)
    (h : π ≫ b = (x ≫ q ≫ a) ≫ c) :
    π ≫ (b ≫ r ≫ s) = x ≫ q ≫ (a ≫ c ≫ r ≫ s) := by
  calc
    _ = (π ≫ b) ≫ r ≫ s := by simp only [Category.assoc]
    _ = ((x ≫ q ≫ a) ≫ c) ≫ r ≫ s := congrArg (fun f => f ≫ r ≫ s) h
    _ = _ := by simp only [Category.assoc]

section Append

variable {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    {L : NextLetter M i} (g : AppendGeometry M L) (output : PrefixScalarModel g.pre)
    {κ : Type u} [κComm : CommRing κ] [tκAlg : Algebra output.T κ]


variable (f : @AppendPriorFibre.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg)
    (C : Type u) [cField : Field C] [cκAlg : Algebra C κ]
    (p : ℕ) [cChar : ExpChar C p] [cPerfect : PerfectRing C p]
    (ps : @AppendPriorSplitting.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar)

/-- The append functional is normalized and preserves each
omitted-letter boundary of its scalar model. -/
theorem append_raw_boundaries (hp : Odd p)
    (X : Scheme.{u}) (baseκ : X ⟶ Spec (.of κ)) (x : X ⟶ output.cT.pt.left)
    (hx : IsPullback x baseκ output.cT.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap output.T κ))))
    (B : Fin (word ++ [i]).length → Over X)
    (bD : ∀ k, (B k).left ⟶ (output.boundaries k).left)
    (hB : ∀ k, IsPullback (B k).hom (bD k) x (output.boundaries k).hom)
    (hrawData : @appendFibreRawData.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
      g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior) g.old g.pre.cG.pt.left g.pre.cG.pt.hom g.pre.m₀ g.d
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg
          output.cT.pt.left X output.qT baseκ x (fun n => (Scheme.Modules.pullback output.qT).obj
  (@matchingModule.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta n)) (fun n =>
      @pullSection.{u} output.cT.pt.left g.pre.cG.pt.left output.qT
  (@matchingModule.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta n)
  (@coefficientMatchingSection.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta
    (fun j => (g.pre.P (singletonIndex j)).coeff 2) g.pre.hr n))
      (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M i L g output.T
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
          (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K
          (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom))
      C cField cκAlg p cChar cPerfect (@AppendPriorFibre.nOpen.{u} K kField kClosed kZero G word M i
          L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.nDir.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.hcPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
      (@AppendPriorSplitting.delta.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hco.{u} K kField kClosed kZero G word M i
          L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hn.{u} K kField kClosed kZero G word M i L
          g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hP.{u} K kField kClosed kZero G word M i L
          g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hr.{u} K kField kClosed kZero G word M i L
          g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps)
      ((@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f).pt.hom
          ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
      (@AppendPriorSplitting.Theta.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.normalized.{u} K kField kClosed kZero G
          word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) hp) :
    let LX := (Scheme.Modules.pullback x).obj ((fun n => (Scheme.Modules.pullback output.qT).obj
  (@matchingModule.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta n)) ((p - 1) / 2))
    let mX := @pullSection.{u} X output.cT.pt.left x ((fun n => (Scheme.Modules.pullback
        output.qT).obj
  (@matchingModule.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta n)) ((p - 1) / 2))
      ((fun n => @pullSection.{u} output.cT.pt.left g.pre.cG.pt.left output.qT
  (@matchingModule.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta n)
  (@coefficientMatchingSection.{u} g.pre.S g.pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) g.pre.S) g.pre.N g.pre.cG g.pre.delta
    (fun j => (g.pre.P (singletonIndex j)).coeff 2) g.pre.hr n)) ((p - 1) / 2))
    ∃ ThetaX : @frobeniusRestriction.{u} C (@Field.toCommRing C cField) p cChar X
        (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ⟶
          SheafOfModules.unit X.ringCatSheaf,
      ThetaX.app ⊤ (mX.app ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) ∧
      ∀ k (V : X.Opens) (a : Γ(X, V)), (B k).hom.app V a = 0 →
        ∀ e : Γ(LX, V), (B k).hom.app V (ThetaX.app V (a • e)) = 0 := by
  classical
  intro LX mX
  obtain ⟨Knode, hopen, hKold, hKbase, hcover, E, ThetaX, SX, hraw, hSX, hnode⟩ := hrawData
  let : ∀ s, IsOpenImmersion (Knode s) := hopen
  let : ∀ {s t} (a : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word
          i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
          kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          output.T) κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg).map
          a).hom.toRingHom)) := (@AppendPriorFibre.nOpen.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
  let : ((((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
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
      output.T output.hMT).toRingHom) tκAlg).op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
    Scheme.forget).IsLocallyDirected) := (@AppendPriorFibre.nDir.{u} K kField kClosed kZero G word M
        i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
  let : IsClosedImmersion g.δ₀ := g.hδClosed
  have hScalar : IsPullback (x ≫ output.qT ≫ AppendChartStage.q g.d) baseκ
      (AppendChartContext.base g.old)
      (Spec.map (CommRingCat.ofHom (algebraMap output.T κ)) ≫
        Spec.map (CommRingCat.ofHom (@algebraMap g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@CommSemiring.toSemiring output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T)) (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring
            K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
            Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom))) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion g.hTpre).toRingHom)) := by
    simpa only [Category.assoc] using hx.paste_horiz (output.hqT.paste_horiz g.hd)
  have hOldπ (s) :
      (((AppendChartContext.eP g.old) s).inv ≫ (AppendChartContext.cD g.old).ι.app (op s)) ≫
        g.qAppend = projectiveToSpec ((AppendChartData.N (@NextLetter.scalarCharts.{u} K kField
            kClosed kZero G word M i L g.coefficients g.prior)).obj s) (ULift.{u} (Fin 2)) ≫
          (g.prior.cT.ι.app (op s)).left :=
    inverse_node_projection ((AppendChartContext.eP g.old) s)
      ((AppendChartContext.cD g.old).ι.app (op s)) g.qAppend (g.π.app (op s))
      (projectiveToSpec ((AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
          word M i L g.coefficients g.prior)).obj s) (ULift.{u} (Fin 2)))
      (g.prior.cT.ι.app (op s)).left (g.hleg s) (g.hπmap s)
  obtain ⟨π, δ, hδ, hδClosed, hπold, hπbase, hδold, hδbase, hπcart, hδcart,
      hnodeπ, hnodeδ, hSδ, hrawδ⟩ :=
    @scalarWord_raw_boundary.{u} C κ M.J cField κComm cκAlg p cChar cPerfect
      (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg)
          (@AppendPriorFibre.nOpen.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.nDir.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.hcPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorSplitting.delta.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hco.{u} K kField kClosed kZero G word M i
          L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hn.{u} K kField kClosed kZero G word M i L
          g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps)
      ((@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f).pt.hom
          ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) (@AppendPriorSplitting.Theta.{u} K kField
          kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps)
      (AppendChartData.sel (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
          g.coefficients g.prior))
      g.prior.cT.pt.left (AppendChartContext.cD g.old).pt (Spec (.of g.prior.T)) X
      g.prior.cT.pt.hom (AppendChartContext.base g.old) g.qAppend g.δ₀ g.hδClosed
      g.hδSection g.hAppendBase.symm (@AppendPriorFibre.q.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f) (x ≫
          output.qT ≫ AppendChartStage.q g.d) baseκ
      (Spec.map (CommRingCat.ofHom (algebraMap output.T κ)) ≫
        Spec.map (CommRingCat.ofHom (@algebraMap g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@CommSemiring.toSemiring output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T)) (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring
            K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
            Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom))) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion g.hTpre).toRingHom))
      (@AppendPriorFibre.hq.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          hScalar (fun s => (AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed kZero
          G word M i L g.coefficients g.prior)).obj s) (fun s => inferInstance)
      (fun s => ((@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
            kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T) κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring
            K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
            Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg).app
            s).hom)
      (fun s => (g.prior.cT.ι.app (op s)).left)
      (fun s => ((AppendChartContext.eP g.old) s).inv ≫ (AppendChartContext.cD g.old).ι.app (op s))
      hOldπ g.hδNode Knode hopen hKold hKbase (@AppendPriorFibre.hleg.{u} K kField kClosed kZero G
          word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f) LX mX
          E ThetaX SX hSX hraw
  refine ⟨ThetaX, ?_, ?_⟩
  · exact (@ProjectiveCartier.twistedSectionOperator_one.{u} C (@Field.toCommRing C cField)
      p cChar X (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ThetaX
      (mX.app ⊤ (1 : Γ(X, ⊤)))).symm.trans
        ((congrArg (fun a : SchemeFrobeniusMap X p => a.onOpen ⊤ 1) hSX).symm.trans
          ((SX.onOpen ⊤).map_one))
  · intro k
    by_cases hk : k.val < word.length
    · let k₀ : Fin word.length := ⟨k.val, hk⟩
      let : IsClosedImmersion (g.prior.boundaries k₀).hom := g.prior.hclosed k₀
      let : IsClosedImmersion ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).hom := by
        change IsClosedImmersion (pullback.fst (@AppendPriorFibre.q.{u} K kField kClosed kZero G
            word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (g.prior.boundaries k₀).hom)
        infer_instance
      let : IsClosedImmersion (B k).hom := by
        rw [← (hB k).isoPullback_hom_fst]
        let : IsClosedImmersion (output.boundaries k).hom := output.hclosed k
        infer_instance
      have hPriorOriginal := ((@AppendPriorFibre.boundary_cartesian.{u} K kField kClosed kZero G
          word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).paste_vert
        ((g.prior.hqB k₀).paste_vert (g.coefficients.hqB k₀))
      have hOriginal := (hB k).paste_vert
        ((output.hqB k).paste_vert (g.hEarlier k hk))
      have hfactor := projection_factor x output.qT (AppendChartStage.q g.d) g.qAppend
        π (@AppendPriorFibre.q.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          g.prior.qT g.coefficients.qT hπold
      have hOriginal' := pullback_right_eq hfactor.symm hOriginal
      have hPrior := IsPullback.of_bot' hOriginal' hPriorOriginal
      choose A gB b hAffine using fun s =>
        @ProjectiveCartier.exists_boundary_affine_chart.{u} ((@fieldRings.{u} K kField kClosed kZero
            g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero
            G word M i L g.coefficients g.prior) output.T κ (@Subalgebra.toCommRing ℤ K
            Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T) κComm
            (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring
            K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
            Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg).obj s)
            (inferInstanceAs (CommRing ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G
            word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
            g.coefficients g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
            (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
            (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
            output.hMT).toRingHom) tκAlg).obj s)))
          (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg
          f).pt.left ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).left ((@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f).ι.app
          (op s)).left
          ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).hom inferInstance
      have hIdeal (s) := @ProjectiveCartier.retainedPrior_kernel.{u} C κ {s : Finset M.J //
          s.Nonempty} (@Field.toCommRing C cField) κComm
        p cChar (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        (inferInstanceAs (Quiver.IsThin {s : Finset M.J // s.Nonempty}))
        (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
            kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T) κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring
            K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
            Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg)
            (@AppendPriorFibre.nOpen.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.nDir.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.hcPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
        ((@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f).pt.hom
          ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
        (@matchingModule.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G
            word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
            g.coefficients g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
            (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
            (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
            output.hMT).toRingHom) tκAlg) (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G
            word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorSplitting.delta.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) ((p - 1) / 2)) (@AppendPriorSplitting.Theta.{u} K kField kClosed
          kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) s
        (retainedMatchingFrameSection (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G
            word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
            g.coefficients g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) κComm (@RingHom.toAlgebra g.pre.S output.T
            (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S) (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T) (@Subalgebra.inclusion ℤ K Int.instCommSemiring (@CommSemiring.toSemiring K
            (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S output.T
            output.hMT).toRingHom) tκAlg) (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G
            word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.hcPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorSplitting.delta.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) ((p - 1) / 2) (@AppendPriorSplitting.hco.{u} K kField kClosed
          kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hn.{u} K kField kClosed kZero G word M i L
          g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps)
          s (AppendChartData.sel (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
              g.coefficients g.prior) s).val (AppendChartData.sel (@NextLetter.scalarCharts.{u} K
              kField kClosed kZero G word M i L g.coefficients g.prior) s).property 1)
        ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).left ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).hom inferInstance
        (A s) (inferInstanceAs (CommRing (A s))) (gB s) (b s) (hAffine s)
            ((@AppendPriorSplitting.boundary.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) k₀)
      exact (@scalarWord_raw_prior.{u} C κ M.J cField κComm cκAlg p cChar cPerfect
        (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior) output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
            kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            output.T) κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
            Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
            g.pre.S) (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring
            K (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
            Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
            (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg)
            (@AppendPriorFibre.nOpen.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.nDir.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorFibre.hcPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          (@AppendPriorSplitting.delta.{u} K kField kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hco.{u} K kField kClosed kZero G word M i
          L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps) (@AppendPriorSplitting.hn.{u} K kField kClosed kZero G word M i L
          g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps)
        ((@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f).pt.hom
          ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) (@AppendPriorSplitting.Theta.{u} K kField
          kClosed kZero G word M i L g
      output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f C
          cField cκAlg p cChar ps)
        (AppendChartData.sel (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
            g.coefficients g.prior)) X ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G
            word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).left (B k).left
        (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX mX ThetaX SX hSX
        Knode hopen E hraw π ((@AppendPriorFibre.boundaries.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f)
          k₀).hom (B k).hom inferInstance _ hPrior
        (fun s => A s) (fun s => inferInstance) gB b hAffine hnodeπ hcover hIdeal).2
    · have hkLast : k.val = word.length := by
        have hkUpper := k.isLt
        simp only [List.length_append, List.length_singleton] at hkUpper
        omega
      have hLast := (hB k).paste_vert ((output.hqB k).paste_vert (g.hLast k hkLast))
      have hLast' : IsPullback (B k).hom
          (bD k ≫ output.qB k ≫ g.lastMap k hkLast)
          (x ≫ output.qT ≫ AppendChartStage.q g.d) g.δ₀ := hLast
      exact @ProjectiveCartier.raw_preserves_of_pullbacks.{u} C (@Field.toCommRing C cField)
        p cChar X (AppendChartContext.cD g.old).pt g.prior.cT.pt.left
        (B k).left (@AppendPriorFibre.cPrior.{u} K kField kClosed kZero G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg
          f).pt.left
        (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ThetaX
        (x ≫ output.qT ≫ AppendChartStage.q g.d) g.δ₀ (B k).hom
        (bD k ≫ output.qB k ≫ g.lastMap k hkLast) δ (@AppendPriorFibre.q.{u} K kField kClosed kZero
            G word M i L
      g output.T κ (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) output.T)
          κComm (@RingHom.toAlgebra g.pre.S output.T (@Subalgebra.toCommSemiring ℤ K
          Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField)) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) output.T) (@Subalgebra.inclusion ℤ K
          Int.instCommSemiring (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K
          (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S output.T output.hMT).toRingHom) tκAlg f) hLast'
          hδcart.flip hrawδ

end Append
end SchubertGeometry.RetainedCharacter
