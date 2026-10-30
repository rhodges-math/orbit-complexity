import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterWeightDecomposition
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialInjective
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.Coalgebra.Comodule.PointAction

/-!
# Torus Point Fixed Weights

The identity-character space of a split-torus action is its
pointwise fixed tangent subspace. -/

noncomputable section
namespace ReductiveGroups
open WithConv

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

variable [Finite ι]

/-- An original tangent vector has identity character for a split-torus
action exactly when every field-valued torus point fixes it under Ad.
The converse uses reduced finite-type point separation on the torus. -/
theorem TorusPointFixedWeights.mem_one_iff_fixed_points
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ affineGroupCharacterWeightSpace π 1 ↔
      ∀ g : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K),
        affineGroupAdjointRepresentation (TauCeti.AlgHom.mapDomain π g) d = d := by
  constructor
  · intro hd g
    rw [AffineGroupAdjoint.eq_character_of_mem_weight π 1 g d hd]
    simp only [← MonoidAlgebra.one_def, map_one, one_smul]
  · intro hfixed
    let f := (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm d
    let _ : TauCeti.Comodule K B (Module.Dual K (TauCeti.Bialgebra.CotangentSpace K B)) :=
      Derivation.adjointComodule (R := K) (H := B)
    let _ : TauCeti.Comodule K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
        (Module.Dual K (TauCeti.Bialgebra.CotangentSpace K B)) :=
      TauCeti.Comodule.Corestrict π.toCoalgHom
    have hpoint (g : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K) :
        TauCeti.Comodule.endOfPoint
            (Module.Dual K (TauCeti.Bialgebra.CotangentSpace K B)) g
            (1 ⊗ₜ[K] f) = 1 ⊗ₜ[K] f := by
      rw [TauCeti.Comodule.endOfPoint_corestrict]
      let pg : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K) :=
        WithConv.toConv g
      have hconj := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
        (CommAlgCat.of K K) (TauCeti.AlgHom.mapDomain π pg) (1 ⊗ₜ[K] f)
      rw [show (TauCeti.AlgHom.mapDomain π pg).ofConv =
        g.comp π.toAlgHom by rfl] at hconj
      apply (Derivation.tangentScalarExtensionEquiv (R := K) (A := B) (B := K)).injective
      rw [hconj]
      have hbase : Derivation.tangentScalarExtensionEquiv
          (R := K) (A := B) (B := K) (1 ⊗ₜ[K] f) = d := by
        ext a
        simp only [Derivation.tangentScalarExtensionEquiv_tmul_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [one_mul]
        calc
          _ = (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K) f) a :=
            (Derivation.cotangentLinearEquiv_apply_apply f a).symm
          _ = d a := by
            change (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)
              ((Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm d)) a =
              d a
            rw [LinearEquiv.apply_symm_apply]
      rw [hbase]
      exact hfixed pg
    have hcoact :=
      (TauCeti.Comodule.coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq f).mpr hpoint
    change f ∈ Derivation.adjointWeightSpace π 1
    rw [Derivation.mem_adjointWeightSpace]
    change (TensorProduct.map LinearMap.id (π : B →ₗc[K] _).toLinearMap
      (TauCeti.Comodule.coact (R := K) (C := B) (M :=
        Module.Dual K (TauCeti.Bialgebra.CotangentSpace K B)) f)) =
      f ⊗ₜ[K] (1 : MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) at hcoact
    simpa only [MonoidAlgebra.one_def] using hcoact

end ReductiveGroups
