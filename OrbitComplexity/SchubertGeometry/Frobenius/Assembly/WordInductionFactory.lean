import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionGeometry
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionApplication
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Constructing the scalar append step

The retained geometry provides the line comparisons and coframe equations.
One append construction returns its scalar model together with its universal
functional, and these witnesses form the next induction step.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private section_character_laws from
  OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter
open private scalar_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private append_scalar_record from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionApplication


namespace SchubertGeometry.RetainedCharacter

private theorem singleton_factor {J : Type u} {C : Type (u + 1)} [Category.{u} C]
    (H : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ C) (X : C)
    (a : ∀ j, H.obj (op (singletonIndex j)) ⟶ X) (j : J) :
    a j = H.map (singletonArrow (singletonIndex j) j (Finset.mem_singleton_self j)).op ≫ a j := by
  rw [show (singletonArrow (singletonIndex j) j (Finset.mem_singleton_self j)).op =
      𝟙 (op (singletonIndex j)) from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem singleton_natural {J : Type u} {C : Type (u + 1)} [Category.{u} C]
    (H : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ C)
    (s t : {s : Finset J // s.Nonempty}) (f : s ⟶ t) (j : J) (hj : j ∈ s.val) :
    H.map f.op ≫ H.map (singletonArrow s j hj).op =
      H.map (singletonArrow t j ((leOfHom f) hj)).op := by
  exact (CategoryTheory.Functor.map_comp H _ _).symm.trans
    (congrArg (fun z => H.map z) (Subsingleton.elim _ _))

private theorem append_step_geometry
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : @PrefixModel.{u} K kField kClosed kZero G word}
    {i : (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {L : @NextLetter.{u} K kField kClosed kZero G word M i}
    (g : @AppendGeometry.{u} K kField kClosed kZero G word M i L) :
    Nonempty (@AppendStep.{u} K kField kClosed kZero G word M i L) := by
  let : Algebra g.prior.T g.pre.S := (Subalgebra.inclusion g.hTpre).toAlgebra
  let : IsScalarTower g.prior.T g.pre.S K :=
    Subalgebra.inclusion.isScalarTower_right g.hTpre K
  have hsingle := @singleton_factor.{u} M.J
    (Over (Spec (.of K))) (inferInstanceAs (Category.{u} (Over (Spec (.of K)))))
    (M.F.op ⋙ algSpec (.of K)) (oppositeUnipotentVariety G).toOver M.a
  have hpn := @singleton_natural.{u} M.J
    (Over (Spec (.of K))) (inferInstanceAs (Category.{u} (Over (Spec (.of K)))))
    (M.F.op ⋙ algSpec (.of K))
  have he₀ := fun (s : {s : Finset M.J // s.Nonempty})
      (x : (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word g.coefficients.prefix
          g.prior.T g.prior.hMT).obj s) =>
    (congrArg (fun f => f x) (@scalar_factor.{u} K kField g.prior.T g.pre.S g.hTpre
      {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
      (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word g.coefficients.prefix g.prior.T
          g.prior.hMT) M.F g.prior.prefix.e s)).trans (g.prior.eValue s x)
  have hmodels := @exists_word_append_splitting.{u}
    K kField kClosed kZero G g.pre.J g.pre.F (@g.pre.fOpen) g.pre.fDir
    (@PrefixModel.fieldCocone.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) g.pre) g.pre.hb word i
        (𝟙 (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))))
    g.pre.point g.pre.a g.pre.ha g.pre.beta g.pre.hgroup (@section_character_laws.{u,u} K kField
        kClosed kZero G g.pre.J g.pre.F g.pre.beta g.pre.hnatural g.pre.hbeta).1
        (@section_character_laws.{u,u} K kField kClosed kZero G g.pre.J g.pre.F g.pre.beta
        g.pre.hnatural g.pre.hbeta).2
    g.pre.S g.pre.N (@g.pre.nOpen) g.pre.nDir g.pre.v g.pre.delta g.pre.hdelta
    g.pre.cG g.pre.hcG g.pre.m₀
    (@PrefixModel.evaluationLeg.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) g.pre)
    g.pre.hco g.pre.hn g.pre.finite
    (@PrefixModel.isSeparated.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) g.pre)
    g.pre.smoothModel g.pre.hv g.pre.P g.pre.hCoefficient g.pre.hm₀
    g.prior.T g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
        g.coefficients g.prior) g.old g.pre.m₀ g.d (@g.prior.nOpen) g.prior.nDir
    g.prior.cT g.π g.hπ g.hπmap g.qAppend g.hleg g.hAppendBase g.hd g.hcD
    g.a₀ g.b₀ g.hD
    g.prior.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
        (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word g.coefficients.prefix
        g.prior.T g.prior.hMT)
    g.prior.v g.prior.P M.a g.hRoot hsingle hpn
    (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty})) g.prior.T g.pre.S (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.prior.T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) g.pre.S) ((Subalgebra.inclusion g.hTpre).toAlgebra)
        (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word g.coefficients.prefix
        g.prior.T g.prior.hMT))
    g.lineIso g.hlineIso he₀ g.πField g.jK g.hV g.hword g.hπField g.hjKb
    g.Q g.hRQ g.pre.e g.pre.eValue (Category.id_comp _) g.hdata
  obtain ⟨out, hraw⟩ := @append_scalar_record.{u}
    K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) g.pre g.Q g.hRQ g.hQ
    (@AppendGeometry.rawData.{u} K kField kClosed kZero G word M i L g) hmodels
  exact ⟨{ geometry := g, output := out, rawStep := hraw }⟩

/-- Construct the scalar append model and its universal functional from a
prefix model and its next-letter charts. -/
theorem exists_append_step
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word)
    (i : (@simpleRootIndex.{u} K kField kClosed kZero G))
    (L : @NextLetter.{u} K kField kClosed kZero G word M i) :
    Nonempty (@AppendStep.{u} K kField kClosed kZero G word M i L) := by
  obtain ⟨g⟩ := @exists_append_geometry.{u} K kField kClosed kZero G word M i L
  exact @append_step_geometry.{u} K kField kClosed kZero G word M i L g

end SchubertGeometry.RetainedCharacter
