import OrbitComplexity.Paper.Deodhar.Products
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Prefix factorization over the complex numbers

Every signed prefix is the ordered product of its selected root elements followed by
the signed representative of its subexpression prefix.
-/

noncomputable section
namespace SchubertOrbits
open BruhatIntervals ReductiveGroups

/-- Each complex signed prefix has its selected-root product factorization. -/
theorem deodhar_inductive_complex (G : ReductiveGroupData ℂ)
    {word : List G.rootBase.support} (expression : Subexpression word)
    (parameters : Fin word.length → ℂ) (n : ℕ) :
    deodharPrefix G expression parameters n =
      subwordRootProduct G expression (fun j => parameters j.val) n *
        subwordRepresentative G expression n :=
  deodharPrefix_rootProduct G expression parameters n

end SchubertOrbits
