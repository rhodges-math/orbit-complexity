import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateWeights
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusCharacterMonomialRelations
import OrbitComplexity.ReductiveGroups.Geometry.DiagonalPolynomialWeights

/-!
# Borel Root Product Support

Support control for arbitrary ordered products of weight Ga
points inside the Borel's Ga-only subgroup. Every monomial of a
dual root coordinate of the logarithm of the product is a monomial
character relation. Factors may repeat and occur in any order. -/

noncomputable section
namespace ReductiveGroups

open TauCeti MvPolynomial

universe u v
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
private theorem splitTorus_point_finsupp_prod'
    {κ : Type*} (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (χ : κ → M) (m : κ →₀ ℕ) :
    t.ofConv (MonoidAlgebra.single (m.prod fun j e => χ j ^ e) 1) =
      m.prod fun j e => t.ofConv (MonoidAlgebra.single (χ j) 1) ^ e := by
  let φ : M →* K := t.ofConv.toMonoidHom.comp (MonoidAlgebra.of K M)
  change φ (m.prod fun j e => χ j ^ e) = m.prod fun j e => φ (χ j) ^ e
  rw [map_finsuppProd]
  simp only [map_pow]

/-- **Support control.** For any finite family of Ga morphisms whose
tangents lie in the Ga-only Borel tangent and in given character
spaces, and any ordered list of them, every monomial of a dual root
coordinate of the logarithm of the ordered product is a monomial relation:
the product of the factor characters with those multiplicities is the
coordinate's own character. -/
theorem borelRootProductLogarithm_support_prod
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val ∈ affineGroupCharacterWeightSpace π i.val)
    {κ : Type v} [Fintype κ] (y : κ → B →ₐc[K] SymmetricAlgebra K K)
    (r : κ → M)
    (hy : ∀ k, gaAffineGroupTangent (y k) ∈ affineGroupCharacterWeightSpace π (r k))
    (hyU : ∀ k, gaAffineGroupTangent (y k) ∈ rootTangentSpace J π hπ)
    (l : List κ) (i : borelRootCharacterIndex J π) (m : κ →₀ ℕ)
    (hm : m ∈ (borelRootProductLogarithm J hJ π hπ y l (e.coord i)).support) :
    (m.prod fun k n => r k ^ n) = i.val := by
  apply splitTorus_character_eq_of_point_eval_eq (K := K) (ν := ι)
  intro t
  rw [splitTorus_point_finsupp_prod']
  apply DiagonalPolynomialWeights.character_of_diagonal_equivariant
    (borelRootProductLogarithm J hJ π hπ y l (e.coord i))
    (fun k (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) =>
      t.ofConv (MonoidAlgebra.single (r k) 1))
    (fun t => t.ofConv (MonoidAlgebra.single i.val 1)) _ m hm t
  intro t a
  exact BorelRootProductLogarithm.diagonal_equivariant J hJ π hπ y hyU l
    (e.coord i) (AlgHom.mapDomain π t)
    (borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t)
    (fun k => t.ofConv (MonoidAlgebra.single (r k) 1))
    (t.ofConv (MonoidAlgebra.single i.val 1))
    (fun k => AffineGroupAdjoint.eq_character_of_mem_weight π (r k) t
      (gaAffineGroupTangent (y k)) (hy k))
    (fun d => borelRootCoordinateBasis_coord_torus_ad I J hJI hI hJ π hπ hker hB
      e he t i d) a

/-- If the coordinate's character is not a monomial in the factor
characters, that dual root coordinate of the logarithm of every ordered
product vanishes identically. -/
theorem BorelRootProductLogarithm.eq_zero_of_not_monomial
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val ∈ affineGroupCharacterWeightSpace π i.val)
    {κ : Type v} [Fintype κ] (y : κ → B →ₐc[K] SymmetricAlgebra K K)
    (r : κ → M)
    (hy : ∀ k, gaAffineGroupTangent (y k) ∈ affineGroupCharacterWeightSpace π (r k))
    (hyU : ∀ k, gaAffineGroupTangent (y k) ∈ rootTangentSpace J π hπ)
    (l : List κ) (i : borelRootCharacterIndex J π)
    (hi : ∀ m : κ →₀ ℕ, (m.prod fun k n => r k ^ n) ≠ i.val) :
    borelRootProductLogarithm J hJ π hπ y l (e.coord i) = 0 := by
  by_contra hne
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty
    (mt MvPolynomial.support_eq_empty.mp hne)
  exact hi m (borelRootProductLogarithm_support_prod I J hJI hI hJ π hπ hker hB
    e he y r hy hyU l i m hm)

/-- Point form: the same dual coordinate of the inverse exponential of every
ordered product of those Ga points vanishes. -/
theorem BorelRootProduct.logarithm_coord_eq_zero_of_not_monomial
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val ∈ affineGroupCharacterWeightSpace π i.val)
    {κ : Type v} [Fintype κ] (y : κ → B →ₐc[K] SymmetricAlgebra K K)
    (r : κ → M)
    (hy : ∀ k, gaAffineGroupTangent (y k) ∈ affineGroupCharacterWeightSpace π (r k))
    (hyU : ∀ k, gaAffineGroupTangent (y k) ∈ rootTangentSpace J π hπ)
    (l : List κ) (i : borelRootCharacterIndex J π)
    (hi : ∀ m : κ →₀ ℕ, (m.prod fun k n => r k ^ n) ≠ i.val) (a : κ → K) :
    e.coord i ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm
      ⟨(l.map (fun k => gaParameterPoint (y k) (a k))).prod,
        GaParameterPoint.prod_mem_of_tangent_mem_quotient y
          (borelRootUnipotentHopfIdeal J π hπ) hyU l a⟩) = 0 := by
  rw [← borelRootProductLogarithm_eval J hJ π hπ y hyU l (e.coord i) a,
    BorelRootProductLogarithm.eq_zero_of_not_monomial I J hJI hI hJ π hπ hker hB
      e he y r hy hyU l i hi, map_zero]

end ReductiveGroups
