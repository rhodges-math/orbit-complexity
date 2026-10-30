import OrbitComplexity.ReductiveGroups.Groups.Representations.UpperMatrixGap
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusMatrixInvariantSubspace
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaInvariantSubspace

/-!
# Matrix Invariant Flags

Upper triangularity means preservation of the basis prefix
subspaces. This transfers simultaneous tangent triangularity to
torus and additive-group point matrices in the same basis. -/

noncomputable section
namespace ReductiveGroups
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}

/-- The equivalence is

```lean
matrixUpperGap 0 (LinearMap.toMatrix b b f) ↔
      ∀ j : Fin n, ∀ v ∈ Submodule.span K (b '' {i : Fin n | i.val ≤ j.val}),
        f v ∈ Submodule.span K (b '' {i : Fin n | i.val ≤ j.val})
```
-/
theorem ToMatrix.upperGap_iff_preserves_basisPrefixes
    (b : Basis (Fin n) K V) (f : Module.End K V) :
    matrixUpperGap 0 (LinearMap.toMatrix b b f) ↔
      ∀ j : Fin n, ∀ v ∈ Submodule.span K (b '' {i : Fin n | i.val ≤ j.val}),
        f v ∈ Submodule.span K (b '' {i : Fin n | i.val ≤ j.val}) := by
  constructor
  · intro h j v hv
    have hle : Submodule.span K (b '' {i : Fin n | i.val ≤ j.val}) ≤
        (Submodule.span K (b '' {i : Fin n | i.val ≤ j.val})).comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change f (b k) ∈ Submodule.span K (b '' {i : Fin n | i.val ≤ j.val})
      rw [b.mem_span_image]
      intro i hi
      change i.val ≤ j.val
      by_contra hij
      have hki : k.val < i.val := by change k.val ≤ j.val at hk; omega
      have hz : b.repr (f (b k)) i = 0 := by
        simpa only [LinearMap.toMatrix_apply] using h i k (by omega)
      exact (Finsupp.mem_support_iff.mp hi) hz
    exact hle hv
  · intro h i j hji
    have hb : b j ∈ Submodule.span K (b '' {k : Fin n | k.val ≤ j.val}) :=
      Submodule.subset_span ⟨j, by change j.val ≤ j.val; exact le_rfl, rfl⟩
    have hs := (b.mem_span_image).mp (h j (b j) hb)
    rw [LinearMap.toMatrix_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hi
    have hij : i.val ≤ j.val := hs hi
    omega

variable [CharZero K]

/-- For these parameters,

```lean
matrixUpperGap 0 (LinearMap.toMatrix b b (Matrix.toLin'
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain q g) :
        Matrix (Fin n) (Fin n) K)))
```
-/
theorem torusMatrixPoint_upper_of_tangents_upper
    {ι : Type*}
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (b : Basis (Fin n) K (Fin n → K))
    (htri : ∀ h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      matrixUpperGap 0 (LinearMap.toMatrix b b
        (Matrix.toLin' (affineGroupMatrixDifferential n q h))))
    (g : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K)) :
    matrixUpperGap 0 (LinearMap.toMatrix b b (Matrix.toLin'
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain q g) :
        Matrix (Fin n) (Fin n) K))) := by
  apply (ToMatrix.upperGap_iff_preserves_basisPrefixes b _).mpr
  intro j v hv
  have hmat : (TauCeti.GeneralLinear.genericMatrix K n).map
      (g.ofConv.comp (q : _ →ₐ[K] _)) =
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain q g) :
        Matrix (Fin n) (Fin n) K) := by
    rw [TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
    rfl
  rw [← hmat]
  apply torusMatrixPoint_preserves_of_tangent K n q _ _ g.ofConv v hv
  intro h w hw
  exact (ToMatrix.upperGap_iff_preserves_basisPrefixes b _).mp (htri h) j w hw

/-- For these parameters,

```lean
matrixUpperGap 0 (LinearMap.toMatrix b b (Matrix.toLin'
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ
        (gaAffineGroupPoints x (Multiplicative.ofAdd t))) :
          Matrix (Fin n) (Fin n) K)))
```
-/
theorem GaAffineGroupMatrixPoint.upper_of_tangent_upper
    {B : Type*} [CommRing B] [HopfAlgebra K B]
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K))
    (htri : matrixUpperGap 0 (LinearMap.toMatrix b b
      (Matrix.toLin' (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x)))))
    (t : K) :
    matrixUpperGap 0 (LinearMap.toMatrix b b (Matrix.toLin'
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ
        (gaAffineGroupPoints x (Multiplicative.ofAdd t))) :
          Matrix (Fin n) (Fin n) K))) := by
  apply (ToMatrix.upperGap_iff_preserves_basisPrefixes b _).mpr
  intro j v hv
  apply GaAffineGroupMatrixPoint.preserves_of_tangent n x ρ _ _ t v hv
  intro w hw
  exact (ToMatrix.upperGap_iff_preserves_basisPrefixes b _).mp htri j w hw

end ReductiveGroups
