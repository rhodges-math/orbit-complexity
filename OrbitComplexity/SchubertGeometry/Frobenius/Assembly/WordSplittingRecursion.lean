import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionPrior
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionFibre
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The carried prior functional on an append fibre

The Cartesian prior fibre carries the original induction functional.
The prescribed coefficient transformation identifies its matching line and
section with the ones consumed by the append operator.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private AppendChartData AppendChartData.N from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private twistModuleMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
open private prior_map_normalized prior_map_boundary polynomial_three_maps
  polynomial_leading_of_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingInduction
open private stageRings terminalRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
open private fieldRings scalarCoefficients fieldPolynomials from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordSplitting

namespace SchubertGeometry.RetainedCharacter

section Prior

variable {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    {L : NextLetter M i} (g : AppendGeometry M L)
    {T κ : Type u} [tComm : CommRing T] [κComm : CommRing κ]
    [sTAlg : Algebra g.pre.S T] [tκAlg : Algebra T κ]
    (f : @AppendPriorFibre.{u} K kField kClosed kZero G word M i L
      g T κ tComm κComm sTAlg tκAlg)
    (C : Type u) [cField : Field C] [cκAlg : Algebra C κ]
    (p : ℕ) [cChar : ExpChar C p]

/-- A normalized matching-line functional on the carried append prior fibre,
with its quadratic transition equations and every omitted-boundary kernel. -/
structure AppendPriorSplitting where
  /-- The carried transition units after coefficient extension. -/
  delta : ∀ (s : {s : Finset M.J // s.Nonempty}) (j : M.J) (_ : j ∈ s.val)
    (k : M.J) (_ : k ∈ s.val), ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg).obj s)ˣ
  /-- The transition-unit cocycle equation. -/
  hco : ∀ s j hj k hk l hl,
    delta s j hj l hl = delta s k hk l hl * delta s j hj k hk
  /-- Naturality of the transition units. -/
  hn : ∀ s t (a : s ⟶ t) j hj k hk,
    Units.map ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg).map a).hom.toMonoidHom (delta s j hj k hk) =
      delta t j ((leOfHom a) hj) k ((leOfHom a) hk)
  /-- The quadratic bound of every retained field polynomial. -/
  hP : ∀ j, ((@fieldPolynomials.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T κ
      tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M
      i L g T tComm sTAlg)) j).natDegree ≤ 2
  /-- The leading-coefficient transition equation. -/
  hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
    ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg).map (singletonArrow s j hj)).hom (((@fieldPolynomials.{u} K
        kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K
        kField kClosed kZero G word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg
        (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M i L g T tComm sTAlg))
        j).coeff 2) =
      ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          T κ tComm κComm sTAlg tκAlg).map (singletonArrow s k hk)).hom (((@fieldPolynomials.{u} K
          kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K
          kField kClosed kZero G word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg
          (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M i L g T tComm
          sTAlg)) k).coeff 2) *
        (delta s j hj k hk : (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
            g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior) T κ tComm κComm sTAlg tκAlg).obj s)
  /-- The matching-line functional of the field fibre. -/
  Theta : @frobeniusRestriction.{u} C (@Field.toCommRing C cField)
    p cChar f.cPrior.pt.left
    (f.cPrior.pt.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
    (@matchingModule.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G
        word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
        g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) f.cPrior delta ((p - 1) / 2)) ⟶
      SheafOfModules.unit f.cPrior.pt.left.ringCatSheaf
  /-- The coefficient section has value one under the functional. -/
  normalized : Theta.app ⊤ (@Scheme.Modules.Hom.app.{u} f.cPrior.pt.left
    (SheafOfModules.unit f.cPrior.pt.left.ringCatSheaf)
    (@matchingModule.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G
        word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
        g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) f.cPrior delta ((p - 1) / 2))
    (@coefficientMatchingSection.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero g.prior.T
        g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
        g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) f.cPrior delta
      (fun j => ((@fieldPolynomials.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          T κ tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G
          word M i L g T tComm sTAlg)) j).coeff 2) hr ((p - 1) / 2))
    ⊤ (1 : Γ(f.cPrior.pt.left, ⊤))) = (1 : Γ(f.cPrior.pt.left, ⊤))
  /-- The functional preserves all carried omitted-boundary kernels. -/
  boundary : ∀ j (U : f.cPrior.pt.left.Opens) (a : Γ(f.cPrior.pt.left, U)),
    (f.boundaries j).hom.app U a = 0 →
      ∀ z : Γ(@matchingModule.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero g.prior.T
          g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
          g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) f.cPrior delta ((p - 1) / 2), U),
        (f.boundaries j).hom.app U (Theta.app U (a • z)) = 0

/-- The carried prefix induction hypothesis gives the normalized prior
functional used by the append operator on this prescribed field fibre. -/
theorem appendPrior_from_induction (hM : PrefixSplits M) (hκField : IsField κ)
    [cPerfect : PerfectRing C p] (hp : Odd p) (hp' : 1 < p) :
    Nonempty (AppendPriorSplitting g f C p) := by
  have hCoeff := @PrefixScalarModel.splits.{u} K kField kClosed kZero G word M
    g.coefficients hM
  have hPrior := @PrefixScalarModel.splits.{u} K kField kClosed kZero G word
    g.coefficients.prefix g.prior hCoeff
  obtain ⟨Theta, hTheta, hBoundary⟩ :=
    @hPrior κ κComm hκField C cField cκAlg p cChar cPerfect hp hp'
      (Spec.map (CommRingCat.ofHom (algebraMap T κ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap g.pre.S T)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion g.hTpre).toRingHom))
      f.cPrior.pt.left f.cPrior.pt.hom f.q f.hq
      f.boundaries f.boundaryMap f.boundary_cartesian
  let delta := @matchingScalarUnits.{u} g.prior.T κ M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u} K kField kClosed kZero
        g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
        word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) g.prior.prefix.delta
  have hco := @matchingScalarUnits_cocycle.{u} g.prior.T κ M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u} K kField kClosed kZero
        g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
        word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) g.prior.prefix.delta
        g.prior.prefix.hco
  have hn := @matchingScalarUnits_natural.{u} g.prior.T κ M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u} K kField kClosed kZero
        g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
        word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) g.prior.prefix.delta
        g.prior.prefix.hn
  have hPM : (@fieldPolynomials.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T κ
      tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M
      i L g T tComm sTAlg)) = @matchingScalarPolynomial.{u} g.prior.T κ M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
      κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
          g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior) T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u} K kField kClosed kZero
          g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
          word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg)
      (fun j => g.prior.P (singletonIndex j)) := by
    exact @polynomial_three_maps.{u} g.prior.T g.pre.S T κ M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
      tComm κComm g.prior.prefix.N
      (@stageRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior))
      (@terminalRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          T tComm sTAlg)
      (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          T κ tComm κComm sTAlg tκAlg)
      (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        g.prior.T g.pre.S
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
              g.prior.T)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        (Subalgebra.inclusion g.hTpre).toAlgebra g.prior.prefix.N)
      (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        g.pre.S T
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
        tComm sTAlg
        (@stageRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior)))
      (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        T κ tComm κComm tκAlg
        (@terminalRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior) T tComm sTAlg))
      (fun j => g.prior.P (singletonIndex j))
  have hP (j : M.J) : ((@fieldPolynomials.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
      g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
      g.prior) T κ tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K kField kClosed
      kZero G word M i L g T tComm sTAlg)) j).natDegree ≤ 2 := by
    rw [congrFun hPM j]
    exact @matchingScalarPolynomial_degree.{u} g.prior.T κ M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
      κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
          g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior) T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u} K kField kClosed kZero
          g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
          word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) (fun j => g.prior.P
          (singletonIndex j))
      (fun j => g.prior.hP (singletonIndex j)) j
  have hr := @polynomial_leading_of_eq.{u} g.prior.T κ M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u} K kField kClosed kZero
        g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
        word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) g.prior.prefix.delta
    (fun j => g.prior.P (singletonIndex j)) (@fieldPolynomials.{u} K kField kClosed kZero g.prior.T
        g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
        g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K
        kField kClosed kZero G word M i L g T tComm sTAlg)) hPM g.prior.hr
  have hLeg : ∀ s, Spec.map ((@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G
      word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
      g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg).app s) ≫ (g.prior.cT.ι.app (op s)).left =
      (f.cPrior.ι.app (op s)).left ≫ f.q := fun s => (f.hleg s).symm
  have hd : ∀ s j hj k hk,
      ((@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          T κ tComm κComm sTAlg tκAlg).app s).hom (g.prior.prefix.delta s j hj k hk :
          g.prior.prefix.N.obj s) =
        (delta s j hj k hk : (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
            g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
            g.prior) T κ tComm κComm sTAlg tκAlg).obj s) := fun _ _ _ _ _ => rfl
  let E := @matchingPullbackIso.{u} g.prior.T κ M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg) (@g.prior.prefix.nOpen) (@f.nOpen)
    g.prior.prefix.nDir f.nDir g.prior.cT g.prior.hcT f.cPrior f.hcPrior
    (@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg) f.q hLeg g.prior.prefix.delta delta hd ((p - 1) / 2)
    g.prior.prefix.hco g.prior.prefix.hn hco hn
  have hv (j : M.J) : ((@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
      g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
      g.prior) T κ tComm κComm sTAlg tκAlg).app (singletonIndex j)).hom
      ((g.prior.P (singletonIndex j)).coeff 2) = ((@fieldPolynomials.{u} K kField kClosed kZero
          g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
          word M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg
          (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M i L g T tComm
          sTAlg)) j).coeff 2 := by
    rw [congrFun hPM j]
    exact (Polynomial.coeff_map _ _).symm
  have hSection := @matchingPullbackIso_section.{u} g.prior.T κ M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    κComm g.prior.prefix.N (@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg) (@g.prior.prefix.nOpen) (@f.nOpen)
    g.prior.prefix.nDir f.nDir g.prior.cT g.prior.hcT f.cPrior f.hcPrior
    (@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg) f.q hLeg g.prior.prefix.delta delta hd ((p - 1) / 2)
    g.prior.prefix.hco g.prior.prefix.hn hco hn
    (fun j => (g.prior.P (singletonIndex j)).coeff 2)
    (fun j => ((@fieldPolynomials.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G
        word M i L g T tComm sTAlg)) j).coeff 2) g.prior.hr hr hv
  let LN := @matchingModule.{u} g.prior.T M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    g.prior.prefix.N g.prior.cT g.prior.prefix.delta ((p - 1) / 2)
  let sN := @coefficientMatchingSection.{u} g.prior.T M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
    g.prior.prefix.N g.prior.cT g.prior.prefix.delta
    (fun j => (g.prior.P (singletonIndex j)).coeff 2) g.prior.hr ((p - 1) / 2)
  let LF := @matchingModule.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero g.prior.T
      g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
      g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) f.cPrior delta ((p - 1) / 2)
  let sF := @coefficientMatchingSection.{u} κ M.J κComm (@fieldRings.{u} K kField kClosed kZero
      g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word
      M i L g.coefficients g.prior) T κ tComm κComm sTAlg tκAlg) f.cPrior delta
    (fun j => ((@fieldPolynomials.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G
        word M i L g T tComm sTAlg)) j).coeff 2) hr ((p - 1) / 2)
  have hInverse : sF ≫ E.inv =
      @pullSection.{u} f.cPrior.pt.left g.prior.cT.pt.left f.q LN sN :=
    (Iso.comp_inv_eq E).2 hSection.symm
  let Phi := @twistModuleMap.{u} C (@Field.toCommRing C cField) p cChar
    f.cPrior.pt.left
    (f.cPrior.pt.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
    LF ((Scheme.Modules.pullback f.q).obj LN) E.inv ≫ Theta
  have hNormalized := @prior_map_normalized.{u} C (@Field.toCommRing C cField)
    p cChar f.cPrior.pt.left
    (f.cPrior.pt.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
    LF ((Scheme.Modules.pullback f.q).obj LN) E.inv sF
    (@pullSection.{u} f.cPrior.pt.left g.prior.cT.pt.left f.q LN sN)
    hInverse Theta hTheta
  have hPreserved := @prior_map_boundary.{u,0} C (@Field.toCommRing C cField)
    p cChar f.cPrior.pt.left
    (f.cPrior.pt.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
    LF ((Scheme.Modules.pullback f.q).obj LN) E.inv Theta
    (Fin word.length) f.boundaries hBoundary
  exact ⟨{ delta := delta
           hco := hco
           hn := hn
           hP := hP
           hr := hr
           Theta := Phi
           normalized := hNormalized
           boundary := hPreserved }⟩

end Prior

end SchubertGeometry.RetainedCharacter
