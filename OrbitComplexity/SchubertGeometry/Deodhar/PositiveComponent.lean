import OrbitComplexity.SchubertGeometry.Deodhar.ComponentIsomorphisms
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterDimensions
import OrbitComplexity.SchubertGeometry.Cells.RichardsonDimension
import OrbitComplexity.BruhatIntervals.Words.Positive

/-! # Positive distinguished components

The unique positive distinguished subexpression has no decreasing step. Its parameter chart
and the Richardson dimension formula identify the dimensions of their varieties.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups BruhatIntervals
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
attribute [local irreducible] deodharParameters deodharComponentIso

/-- A reduced word has a unique positive distinguished subexpression for each lower endpoint,
and its component has the dimension of the Richardson variety. -/
theorem positive_distinguished_component
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (a b : G.weylGroup)
    (hword : (weylCoxeterSystem G.rootBase).wordProd word = b)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    (∀ expression : Subexpression word,
      IsPositive (weylCoxeterSystem G.rootBase) expression ↔
        negativeSteps (weylCoxeterSystem G.rootBase) expression = ∅) ∧
    ∃ expression : Subexpression word,
      expression.prefixProd (weylCoxeterSystem G.rootBase) word.length = a ∧
      IsDistinguished (weylCoxeterSystem G.rootBase) expression ∧
      IsPositive (weylCoxeterSystem G.rootBase) expression ∧
      (deodharComponent G expression hred).dim = (richardsonVariety G a b).dim ∧
      ∀ other : Subexpression word,
        other.prefixProd (weylCoxeterSystem G.rootBase) word.length = a →
        IsDistinguished (weylCoxeterSystem G.rootBase) other →
        IsPositive (weylCoxeterSystem G.rootBase) other → other = expression := by
  refine ⟨fun expression => isPositive_iff_negativeSteps_empty
    (weylCoxeterSystem G.rootBase) expression, ?_⟩
  have hle' : (weylCoxeterSystem G.rootBase).BruhatLE a
      ((weylCoxeterSystem G.rootBase).wordProd word) := by
    rwa [hword]
  obtain ⟨expression, he, hunique⟩ := positive_subexpression_unique
    (weylCoxeterSystem G.rootBase) hred a hle'
  refine ⟨expression, he.1, he.2.1, he.2.2, ?_, ?_⟩
  · let e : (deodharParameters G expression).toOver ≅
        (deodharComponent G expression hred).toOver :=
      deodharComponentIso G expression hred he.2.1
    have hc := (Variety.dim_eq_of_iso (deodharParameters G expression) e).symm.trans
      (positiveParameters_dim G expression he.2.2)
    have hn : word.length = (weylCoxeterSystem G.rootBase).length b :=
      hred.eq.symm.trans (congrArg (weylCoxeterSystem G.rootBase).length hword)
    rw [he.1, hn] at hc
    exact hc.trans (richardsonVariety_dim G a b hle).symm
  · intro other hfinal hdistinguished hpositive
    exact hunique other ⟨hfinal, hdistinguished, hpositive⟩

end
end SchubertGeometry
