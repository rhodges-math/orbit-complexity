import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorMorphisms

/-! # Finite input-weighted sums of Frobenius-linear sheaf operators -/

namespace FrobeniusSplitting
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u v

namespace FrobeniusLinearMap
variable {R : Type*} [CommSemiring R] {p : ℕ} {ι : Type*} [Fintype ι]

/-- A finite input-weighted sum is a Frobenius-linear operator. -/
def inputSum (φ : ι → FrobeniusLinearMap R p) (c : ι → R) : FrobeniusLinearMap R p where
  toAddMonoidHom :=
    { toFun a := ∑ i, φ i (c i * a)
      map_zero' := by simp only [mul_zero, FrobeniusLinearMap.map_zero, Finset.sum_const_zero]
      map_add' a b := by
        simp only [mul_add, FrobeniusLinearMap.map_add, Finset.sum_add_distrib] }
  map_pow_mul' a b := by
    change (∑ i, (φ i).weight (c i) (a ^ p * b)) = a * ∑ i, (φ i).weight (c i) b
    simp only [FrobeniusLinearMap.map_pow_mul, Finset.mul_sum]

private theorem inputSum_apply (φ : ι → FrobeniusLinearMap R p) (c : ι → R) (a : R) :
    inputSum φ c a = ∑ i, φ i (c i * a) := rfl

private theorem inputSum_localize {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : ℕ} (φ : ι → FrobeniusLinearMap R p) (c : ι → R)
    (M : Submonoid R) [IsLocalization M S] (hp : 0 < p) :
    (inputSum φ c).localize (S := S) M hp =
      inputSum (fun i => (φ i).localize (S := S) M hp) (fun i => algebraMap R S (c i)) := by
  apply localize_eq
  intro a
  simp only [inputSum_apply, ← map_mul, localize_algebraMap, map_sum]

end FrobeniusLinearMap

namespace SchemeFrobeniusMap
variable {X : Scheme.{u}} {p : ℕ} {ι : Type v} [Fintype ι]

/-- Global section weights act on inputs, before summing the sheaf operators. -/
def inputSum (φ : ι → SchemeFrobeniusMap X p) (c : ι → Γ(X, ⊤)) :
    SchemeFrobeniusMap X p where
  onOpen U := FrobeniusLinearMap.inputSum (fun i => (φ i).onOpen U)
    (fun i => X.presheaf.map (homOfLE le_top).op (c i))
  restrict_comm {U V} h s := by
    simp only [FrobeniusLinearMap.inputSum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hc : X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE le_top).op (c i)) =
          X.presheaf.map (homOfLE le_top).op (c i) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [← (φ i).restrict_comm h]
    congr 1
    rw [map_mul, hc]

end SchemeFrobeniusMap

namespace SchemeFrobeniusMap
variable {X Y : Scheme.{u}} {p : ℕ} {ι : Type v} [Fintype ι]

/-- Input-weighted sums commute with a morphism preserving their operators and global weights. -/
theorem inputSum_naturality (f : Y ⟶ X)
    (φ : ι → SchemeFrobeniusMap X p) (ψ : ι → SchemeFrobeniusMap Y p)
    (c : ι → Γ(X, ⊤)) (d : ι → Γ(Y, ⊤))
    (hc : ∀ i, f.appTop (c i) = d i)
    (hφ : ∀ i (V : X.Opens) (s : Γ(X, V)),
      (ψ i).onOpen (f ⁻¹ᵁ V) (f.app V s) = f.app V ((φ i).onOpen V s))
    (V : X.Opens) (s : Γ(X, V)) :
    (inputSum ψ d).onOpen (f ⁻¹ᵁ V) (f.app V s) =
      f.app V ((inputSum φ c).onOpen V s) := by
  simp only [inputSum, FrobeniusLinearMap.inputSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcoeff : f.app V (X.presheaf.map (homOfLE le_top).op (c i)) =
      Y.presheaf.map (homOfLE le_top).op (d i) := by
    have h := congrArg (fun g : Γ(X, ⊤) ⟶ Γ(Y, f ⁻¹ᵁ V) => g (c i))
      (f.naturality (homOfLE le_top).op)
    change f.app V (X.presheaf.map (homOfLE le_top).op (c i)) =
      Y.presheaf.map (homOfLE le_top).op (f.appTop (c i)) at h
    exact h.trans (congrArg (Y.presheaf.map (homOfLE le_top).op) (hc i))
  rw [← hφ]
  congr 1
  rw [map_mul, hcoeff]

end SchemeFrobeniusMap

namespace FrobeniusLinearMap
variable {R : Type u} [CommRing R] {p : ℕ} {ι : Type v} [Fintype ι]

/-- Finite input-weighted sums commute with forming the operators on an affine spectrum. -/
theorem inputSum_toSpec (φ : ι → FrobeniusLinearMap R p) (c : ι → R) (hp : 0 < p) :
    (inputSum φ c).toSpec hp =
      SchemeFrobeniusMap.inputSum (fun i => (φ i).toSpec hp)
        (fun i => StructureSheaf.toOpenₗ R R ⊤ (c i)) := by
  apply SchemeFrobeniusMap.ext
  intro U s
  apply Subtype.ext
  funext x
  change (inputSum φ c).localize (S := Localization x.1.asIdeal.primeCompl)
      x.1.asIdeal.primeCompl hp (s.1 x) = _
  rw [inputSum_localize, inputSum_apply]
  let ev : Γ(Spec (.of R), U) →+ Localization x.1.asIdeal.primeCompl :=
    { toFun f := f.1 x
      map_zero' := rfl
      map_add' _ _ := rfl }
  change (∑ i, (φ i).localize (S := Localization x.1.asIdeal.primeCompl)
      x.1.asIdeal.primeCompl hp (algebraMap R _ (c i) * s.1 x)) =
    ev (∑ i, ((φ i).toSpec hp).onOpen U
      ((Spec (.of R)).presheaf.map (homOfLE le_top).op
        (StructureSheaf.toOpenₗ R R ⊤ (c i)) * s))
  rw [map_sum]
  rfl

end FrobeniusLinearMap

end
end FrobeniusSplitting
