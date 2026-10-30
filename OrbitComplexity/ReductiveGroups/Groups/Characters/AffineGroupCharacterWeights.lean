import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation
import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Affine Group Character Weights

Character weight spaces on the original tangent derivations.
The coordinate map is an explicit argument; the definition does not require
a maximal torus or reductivity. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

universe u
variable {K B M : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CommGroup M]

/-- The character weight space of a diagonalizable subgroup action, on the
original group's counit-valued tangent derivations. -/
def affineGroupCharacterWeightSpace
    (π : B →ₐc[K] MonoidAlgebra K M) (α : M) :
    Submodule K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :=
  (Derivation.adjointWeightSpace π α).comap
    (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm.toLinearMap

/-- The equivalence is

```lean
d ∈ affineGroupCharacterWeightSpace π α ↔
      (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm d ∈
        Derivation.adjointWeightSpace π α
```
-/
@[simp] theorem mem_affineGroupCharacterWeightSpace
    (π : B →ₐc[K] MonoidAlgebra K M) (α : M)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ affineGroupCharacterWeightSpace π α ↔
      (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm d ∈
        Derivation.adjointWeightSpace π α := Iff.rfl

/-- The tangent Lie bracket respects the character grading. -/
theorem lie_mem_affineGroupCharacterWeightSpace
    (π : B →ₐc[K] MonoidAlgebra K M) (α β : M)
    (d e : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ affineGroupCharacterWeightSpace π α)
    (he : e ∈ affineGroupCharacterWeightSpace π β) :
    ⁅d, e⁆ ∈ affineGroupCharacterWeightSpace π (α * β) := by
  change (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm ⁅d, e⁆ ∈
    Derivation.adjointWeightSpace π (α * β)
  have hbr := (Derivation.cotangentDualLieEquiv (R := K) (H := B)).symm.map_lie d e
  simp only [Derivation.cotangentDualLieEquiv_symm_apply] at hbr
  rw [hbr]
  exact Derivation.lie_mem_adjointWeightSpace_mul hd he

private theorem tangentScalarExtension_tmul_base (c : K)
    (f : Module.Dual K (TauCeti.Bialgebra.CotangentSpace K B)) :
    Derivation.tangentScalarExtensionEquiv (R := K) (A := B) (B := K)
      (c ⊗ₜ[K] f) =
        c • Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K) f := by
  ext b
  simp only [Derivation.tangentScalarExtensionEquiv_tmul_apply,
    Derivation.smul_apply, Derivation.cotangentLinearEquiv_apply_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  rfl

/-- The group point acts on a character weight vector by the
value of that same character at the diagonalizable-group point. -/
theorem AffineGroupAdjoint.eq_character_of_mem_weight
    (π : B →ₐc[K] MonoidAlgebra K M) (α : M)
    (g : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ affineGroupCharacterWeightSpace π α) :
    affineGroupAdjointRepresentation (TauCeti.AlgHom.mapDomain π g) d =
      g.ofConv (MonoidAlgebra.single α 1) • d := by
  let f := (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm d
  have hf : f ∈ Derivation.adjointWeightSpace π α := hd
  have hweight := Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace π g.ofConv 1 hf
  have hconj := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (CommAlgCat.of K K) (TauCeti.AlgHom.mapDomain π g) (1 ⊗ₜ[K] f)
  have hpoint : Derivation.pointInCounitAlgebra K (TauCeti.AlgHom.mapDomain π g) =
      (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm
        (TauCeti.AlgHom.mapDomain π g) := rfl
  rw [hpoint] at hconj
  rw [show (TauCeti.AlgHom.mapDomain π g).ofConv =
    g.ofConv.comp π.toAlgHom by rfl, hweight] at hconj
  simp only [one_mul, tangentScalarExtension_tmul_base, one_smul,
    f, LinearEquiv.apply_symm_apply] at hconj
  exact hconj.symm

variable [CharZero K]

/-- A subgroup with tangent in the character weight space obeys the
root-parametrization conjugation law with that character's value. -/
theorem GaAffineGroupPoints.conjugate_of_character_weight
    (π : B →ₐc[K] MonoidAlgebra K M) (α : M)
    (g : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α) (t : K) :
    TauCeti.AlgHom.mapDomain π g * gaAffineGroupPoints x (Multiplicative.ofAdd t) *
        (TauCeti.AlgHom.mapDomain π g)⁻¹ =
      gaAffineGroupPoints x
        (Multiplicative.ofAdd (g.ofConv (MonoidAlgebra.single α 1) * t)) := by
  apply gaAffineGroupPoints_conjugate_of_weight x (TauCeti.AlgHom.mapDomain π g)
  exact AffineGroupAdjoint.eq_character_of_mem_weight π α g _ hx

end ReductiveGroups
