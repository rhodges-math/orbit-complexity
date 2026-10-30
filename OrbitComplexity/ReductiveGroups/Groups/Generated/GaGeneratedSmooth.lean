import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedPointClosure
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-!
# Ga Generated Smooth

Smoothness of the Ga-generated closed subgroup follows from its
proved reducedness over the algebraically closed ground field. -/

noncomputable section
namespace ReductiveGroups

universe u v
variable {K B : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] {ι : Type v}

/-- Any family of additive one-parameter groups generates a smooth closed
subgroup. The quotient is the common-kernel Hopf quotient already constructed. -/
theorem gaGeneratedQuotient_smooth
    (f : ι → B →ₐc[K] SymmetricAlgebra K K) :
    TauCeti.smoothCommHopfAlgProperty K
      (TauCeti.CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
        (gaGeneratedHopfIdeal f)) := by
  exact TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _

end ReductiveGroups
