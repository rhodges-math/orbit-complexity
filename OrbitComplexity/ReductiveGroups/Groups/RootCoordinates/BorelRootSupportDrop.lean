import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubset

/-!
# Borel Root Support Drop

Ordered root products whose nonzero parameters all sit on roots of a
closed set `S` lie in `U_S`: factors with zero parameter are trivial and do
not contribute to any monomial of the logarithm coordinates. -/

noncomputable section
namespace ReductiveGroups

open TauCeti MvPolynomial

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

omit [IsAlgClosed K] [CharZero K] [Finite ι] in
/-- Closedness applied to a monomial relation whose exponents are supported
on indices with characters in `S`. -/
theorem IsBorelRootCharacterClosed.mem_of_prod_support
    {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    {S : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    {κ : Type*} (r : κ → borelRootCharacterIndex J π)
    (m : κ →₀ ℕ) (hr : ∀ k ∈ m.support, r k ∈ S) (i : borelRootCharacterIndex J π)
    (h : (m.prod fun k n => (r k).val ^ n) = i.val) : i ∈ S := by
  classical
  apply hS (m.mapDomain r) i
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hj)
    exact hr k hk
  · rw [borelRootCharacter_prod_mapDomain, h]

/-- **Products with sparse parameters.** If every factor with a nonzero
parameter has its character in the closed set `S`, the ordered product lies
in `U_S`. -/
theorem BorelRootProduct.mem_subsetPoints_of_support
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val ∈ affineGroupCharacterWeightSpace π i.val)
    {S : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    {κ : Type u} [Fintype κ] (y : κ → B →ₐc[K] SymmetricAlgebra K K)
    (r : κ → borelRootCharacterIndex J π)
    (hy : ∀ k, gaAffineGroupTangent (y k) ∈ affineGroupCharacterWeightSpace π (r k).val)
    (hyU : ∀ k, gaAffineGroupTangent (y k) ∈ rootTangentSpace J π hπ)
    (l : List κ) (a : κ → K) (hra : ∀ k, a k ≠ 0 → r k ∈ S) :
    (⟨(l.map (fun k => gaParameterPoint (y k) (a k))).prod,
        GaParameterPoint.prod_mem_of_tangent_mem_quotient y
          (borelRootUnipotentHopfIdeal J π hπ) hyU l a⟩ :
      borelRootUnipotentPoints J π hπ) ∈ borelRootSubsetPoints J hJ π hπ e S := by
  classical
  intro i hi
  rw [← borelRootProductLogarithm_eval J hJ π hπ y hyU l (e.coord i) a]
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Finset.sum_eq_zero
  intro m hm
  by_cases hzero : ∃ k ∈ m.support, a k = 0
  · obtain ⟨k, hk, hak⟩ := hzero
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero hk
    rw [hak, zero_pow (Finsupp.mem_support_iff.mp hk)]
  · push Not at hzero
    exfalso
    apply hi
    exact hS.mem_of_prod_support r m (fun k hk => hra k (hzero k hk)) i
      (borelRootProductLogarithm_support_prod I J hJI hI hJ π hπ hker hB e he y
        (fun k => (r k).val) hy hyU l i m hm)

end ReductiveGroups
