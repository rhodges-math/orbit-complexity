import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic

/-!
# Hopf Ideal Normal Base Change

Normal closed subgroups remain normal after scalar extension. The proof
uses all algebra-valued points, not only points of the ground field. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K L : Type u} [CommRing K] [CommRing L] [Algebra K L]

/-- Base change preserves the coordinate definition of normality of a
closed subgroup. -/
theorem hopfIdeal_isNormal_baseChange
    (B : CommHopfAlgCat.{u} K) (I : TauCeti.HopfIdeal K B) (hI : I.IsNormal) :
    (TauCeti.CommHopfAlgCat.baseChangeHopfIdeal (K := L) I).IsNormal := by
  apply (TauCeti.CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal _ _).mpr
  intro A
  refine ⟨fun n hn g => ?_⟩
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_baseChangeHopfIdeal_iff] at hn ⊢
  have hnormal := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal B I hI
    (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap K L) A)
  simpa only [map_mul, map_inv] using hnormal.conj_mem
    (TauCeti.CommHopfAlgCat.baseChangePointsMulEquiv (K := L) A B n) hn
    (TauCeti.CommHopfAlgCat.baseChangePointsMulEquiv (K := L) A B g)

end ReductiveGroups
