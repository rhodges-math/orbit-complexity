import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateBasis
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootTorusCoordinates
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductEquivariance

/-!
# Borel Root Coordinate Weights

The dual coordinates of the root tangent basis transform
by the torus characters. This proves covariance of the
ordered-product logarithm polynomial in those coordinates. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

/-- In an eigenvector basis, evaluating a coordinate after the linear
endomorphism multiplies that coordinate by its eigenvalue. -/
theorem basis_coord_map_of_eigenvectors {K V κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] (e : Module.Basis κ K V)
    (A : V →ₗ[K] V) (c : κ → K)
    (he : ∀ i, A (e i) = c i • e i) (i : κ) (v : V) :
    e.coord i (A v) = c i * e.coord i v := by
  classical
  have h : (e.coord i).comp A = c i • e.coord i := by
    apply e.ext
    intro j
    simp only [LinearMap.comp_apply, he, map_smul, LinearMap.smul_apply]
    by_cases hij : i = j
    · subst j
      rfl
    · simp [Module.Basis.coord_apply, hij]
  exact congrArg (fun f : V →ₗ[K] K => f v) h

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

variable (I J : HopfIdeal K B) (hJI : J ≤ I)
  (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
  (hπ : Function.Surjective π)
  (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
  (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

/-- Original torus conjugation acts diagonally on the dual of a
character-indexed root basis. -/
theorem borelRootCoordinateBasis_coord_torus_ad
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val ∈ affineGroupCharacterWeightSpace π i.val)
    (t : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K))
    (i : borelRootCharacterIndex J π) (d : rootTangentSpace J π hπ) :
    e.coord i ⟨affineGroupAdjointRepresentation (AlgHom.mapDomain π t) d.val,
      borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t d⟩ =
        t.ofConv (MonoidAlgebra.single i.val 1) * e.coord i d := by
  let A : rootTangentSpace J π hπ →ₗ[K] rootTangentSpace J π hπ :=
    ((affineGroupAdjointRepresentation (AlgHom.mapDomain π t)).comp
      (rootTangentSpace J π hπ).incl.toLinearMap).codRestrict
        (rootTangentSpace J π hπ).toSubmodule
        (borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t)
  apply basis_coord_map_of_eigenvectors e A
    (fun j => t.ofConv (MonoidAlgebra.single j.val 1)) _ i d
  intro j
  apply Subtype.ext
  exact AffineGroupAdjoint.eq_character_of_mem_weight π j.val t (e j).val (he j)

include hJI hI hker hB in
/-- In root basis coordinates, the product-logarithm polynomial
has the required diagonal torus covariance, for every ordered list. -/
theorem BorelRootCoordinateProduct.torus_equivariant
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    (l : List (borelRootCharacterIndex J π))
    (t : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K))
    (i : borelRootCharacterIndex J π) (a : borelRootCharacterIndex J π → K) :
    MvPolynomial.aeval (fun j => t.ofConv (MonoidAlgebra.single j.val 1) * a j)
        (borelRootProductLogarithm J hJ π hπ x l (e.coord i)) =
      t.ofConv (MonoidAlgebra.single i.val 1) *
        MvPolynomial.aeval a (borelRootProductLogarithm J hJ π hπ x l (e.coord i)) := by
  have hxU (j) : gaAffineGroupTangent (x j) ∈ rootTangentSpace J π hπ :=
    he j ▸ (e j).property
  apply BorelRootProductLogarithm.diagonal_equivariant J hJ π hπ x hxU l
    (e.coord i) (AlgHom.mapDomain π t)
    (borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t)
  · intro j
    exact AffineGroupAdjoint.eq_character_of_mem_weight π j.val t
      (gaAffineGroupTangent (x j)) (hx j)
  · intro d
    exact borelRootCoordinateBasis_coord_torus_ad I J hJI hI hJ π hπ hker hB
      e (fun j => he j ▸ hx j) t i d

end ReductiveGroups
