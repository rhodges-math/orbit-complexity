import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorSpec
import OrbitComplexity.FrobeniusSplitting.Splittings.Spec

/-! # Forgetting the normalization of a Frobenius splitting -/

namespace FrobeniusSplitting
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

/-- A ring splitting is a Frobenius-linear operator after forgetting its value at one. -/
def RingSplitting.toOperator {R : Type*} [CommSemiring R] {p : ℕ}
    (base : RingSplitting R p) : FrobeniusLinearMap R p where
  toAddMonoidHom := base.toAddMonoidHom
  map_pow_mul' := base.map_pow_mul

/-- A scheme splitting gives a Frobenius-linear structure-sheaf operator. -/
def SchemeSplitting.toOperator {X : Scheme} {p : ℕ} (splitting : SchemeSplitting X p) :
    SchemeFrobeniusMap X p where
  onOpen U := (splitting.onOpen U).toOperator
  restrict_comm := splitting.restrict_comm

private theorem operator_localize {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : ℕ} (base : RingSplitting R p) (M : Submonoid R) [IsLocalization M S]
    (hp : 0 < p) (a : S) :
    base.toOperator.localize M hp a = base.localize M hp a := by
  have h := base.toOperator.localize_eq (S := S) M hp
    (base.localize (S := S) M hp).toOperator
      (fun r => base.localize_algebraMap (S := S) M hp r)
  exact congrArg (fun φ : FrobeniusLinearMap S p => φ a) h

/-- Forgetting normalization commutes with the operator on the affine spectrum. -/
theorem RingSplitting.toOperator_toSpec {R : Type u} [CommRing R] {p : ℕ}
    (base : RingSplitting R p) (hp : 0 < p) :
    (base.toSpec hp).toOperator = base.toOperator.toSpec hp := by
  apply SchemeFrobeniusMap.ext
  intro U s
  apply Subtype.ext
  funext x
  change base.localize (S := Localization x.1.asIdeal.primeCompl)
      x.1.asIdeal.primeCompl hp (s.1 x) =
    base.toOperator.localize (S := Localization x.1.asIdeal.primeCompl)
      x.1.asIdeal.primeCompl hp (s.1 x)
  exact (operator_localize base x.1.asIdeal.primeCompl hp (s.1 x)).symm

end
end FrobeniusSplitting
