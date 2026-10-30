import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Borel Maximality Base Change

Minimality of the fixed original Borel ideal against an
algebraic-closure base-changed Borel candidate. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K : Type u} [Field K]

/-- Borel minimality descends from its defining algebraic-closure extension
to the original Hopf ideal order.  -/
theorem borel_minimal_baseChangeCandidate
    (H : FiniteTypeCommHopfAlgCat.{u,u} K)
    (J Q : HopfIdeal K H)
    (hJ : HopfIdeal.IsBorel K H.obj J)
    (hQJ : Q ≤ J)
    (hQ : HopfIdeal.IsBorelCandidate (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure K) Q)) :
    J ≤ Q := by
  let C := AlgebraicClosure K
  have hmax := ((HopfIdeal.isBorel_iff K H.obj J).mp hJ).2.2.2
  have hbase : CommHopfAlgCat.baseChangeHopfIdeal (K := C) J ≤
      CommHopfAlgCat.baseChangeHopfIdeal (K := C) Q :=
    hmax (CommHopfAlgCat.baseChangeHopfIdeal (K := C) Q)
      hQ.1 hQ.2.1 hQ.2.2
      (CommHopfAlgCat.baseChangeHopfIdeal_mono (K := C) hQJ)
  exact (CommHopfAlgCat.baseChangeHopfIdeal_le_iff (K := C)
    (FaithfulSMul.algebraMap_injective K C)).mp hbase

end ReductiveGroups
