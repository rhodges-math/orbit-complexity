import OrbitComplexity.ReductiveGroups.Lie.Roots.MatrixBasisConjugation
import OrbitComplexity.ReductiveGroups.Groups.Solvable.GeneratedTriangularSolvability
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints

/-!
# Faithful Matrix Basis

Changing a faithful coordinate representation to a basis
preserves faithfulness of the original point group. -/

noncomputable section
namespace ReductiveGroups
open Module WithConv CategoryTheory

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B] {n : ℕ}

/-- The equality is

```lean
∃ τ : WithConv (B →ₐ[K] K) →* (Matrix (Fin n) (Fin n) K)ˣ,
      Function.Injective τ ∧ ∀ g,
        (τ g : Matrix (Fin n) (Fin n) K) =
          LinearMap.toMatrix b b (Matrix.toLin'
            (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ g) :
              Matrix (Fin n) (Fin n) K))
```
-/
theorem exists_faithful_matrixPoints_in_basis
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) (b : Basis (Fin n) K (Fin n → K)) :
    ∃ τ : WithConv (B →ₐ[K] K) →* (Matrix (Fin n) (Fin n) K)ˣ,
      Function.Injective τ ∧ ∀ g,
        (τ g : Matrix (Fin n) (Fin n) K) =
          LinearMap.toMatrix b b (Matrix.toLin'
            (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ g) :
              Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨P, hP⟩ := exists_matrixBasisConjugation n b
  let f := (TauCeti.GeneralLinear.pointsMulEquiv (R := K) (A := K) n).toMonoidHom.comp
    (TauCeti.AlgHom.mapDomain ρ)
  have hf : Function.Injective f := by
    intro g h hgh
    have hp := (TauCeti.GeneralLinear.pointsMulEquiv (R := K) (A := K) n).injective hgh
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    obtain ⟨z, rfl⟩ := hρ a
    exact congrArg (fun p : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) => p.ofConv z) hp
  let τ := (MulAut.conj P).toMonoidHom.comp f
  refine ⟨τ, (MulAut.conj P).injective.comp hf, ?_⟩
  intro g
  change ((P * f g * P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
    Matrix (Fin n) (Fin n) K) = _
  simpa only [Units.val_mul, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    using hP (f g : Matrix (Fin n) (Fin n) K)

universe u v
variable {K' : Type u} [Field K'] [IsAlgClosed K'] {ι : Type v}
  (H : CommHopfAlgCat.{u} K') (D : ι → CommHopfAlgCat.{u} K')
  [∀ i, Algebra.FiniteType K' (D i)] [∀ i, IsReduced (D i)]

/-- For these parameters,

```lean
TauCeti.HopfIdeal.IsBorelCandidate K'
      ⟨H, (TauCeti.finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal f)
```
-/
theorem CommonKernelQuotient.borelCandidate_of_matrixBasis
    [Algebra.FiniteType K' H] [∀ i, ConnectedSpace (PrimeSpectrum (D i))]
    (f : ∀ i, H ⟶ D i)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K' n →ₐc[K'] H)
    (hρ : Function.Surjective ρ) (b : Basis (Fin n) K' (Fin n → K'))
    (htri : ∀ i (p : WithConv (D i →ₐ[K'] K')),
      matrixUpperGap 0 (LinearMap.toMatrix b b (Matrix.toLin'
        (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain ρ
            (toConv (p.ofConv.comp ((f i).hom : H →ₐ[K'] D i)))) :
              Matrix (Fin n) (Fin n) K')))) :
    TauCeti.HopfIdeal.IsBorelCandidate K'
      ⟨H, (TauCeti.finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal f) := by
  obtain ⟨τ, hτ, hτmat⟩ := exists_faithful_matrixPoints_in_basis ρ hρ b
  apply CommonKernelQuotient.borelCandidate_of_triangular H D f τ hτ
  intro i p
  rw [hτmat]
  exact htri i p

end ReductiveGroups
