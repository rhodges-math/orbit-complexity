import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCharacterHeights
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateWeights
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductChart
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusCharacterMonomialRelations
import OrbitComplexity.ReductiveGroups.Geometry.DiagonalPolynomialWeights

/-!
# Product Polynomial Equiv

The ordered root-product logarithm, in the dual coordinates of
the original root tangent basis, is a positive-weight triangular polynomial
automorphism. Positive weights are the root heights for the base selected
by the Borel. -/

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
private theorem splitTorus_point_finsupp_prod
    {κ : Type*} (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (χ : κ → M) (m : κ →₀ ℕ) :
    t.ofConv (MonoidAlgebra.single (m.prod fun j e => χ j ^ e) 1) =
      m.prod fun j e => t.ofConv (MonoidAlgebra.single (χ j) 1) ^ e := by
  let φ : M →* K := t.ofConv.toMonoidHom.comp (MonoidAlgebra.of K M)
  change φ (m.prod fun j e => χ j ^ e) = m.prod fun j e => φ (χ j) ^ e
  rw [map_finsuppProd]
  simp only [map_pow]

/-- Every monomial occurring in an ordered-product logarithm
coordinate is a monomial relation among the Borel root characters:
its character product is the coordinate's own character. -/
theorem BorelRootProductLogarithm.support_character
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    (l : List (borelRootCharacterIndex J π)) (i : borelRootCharacterIndex J π)
    (m : borelRootCharacterIndex J π →₀ ℕ)
    (hm : m ∈ (borelRootProductLogarithm J hJ π hπ x l (e.coord i)).support) :
    (m.prod fun j k => j.val ^ k) = i.val := by
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  let _ : Fintype (borelRootCharacterIndex J π) := Fintype.ofFinite _
  apply splitTorus_character_eq_of_point_eval_eq (K := K) (ν := ι)
  intro t
  rw [splitTorus_point_finsupp_prod]
  apply DiagonalPolynomialWeights.character_of_diagonal_equivariant
    (borelRootProductLogarithm J hJ π hπ x l (e.coord i))
    (fun j (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) =>
      t.ofConv (MonoidAlgebra.single j.val 1))
    (fun t => t.ofConv (MonoidAlgebra.single i.val 1)) _ m hm t
  intro t a
  exact BorelRootCoordinateProduct.torus_equivariant I J hJI hI hJ π hπ hker hB
      x e he hx l t i a

/-- Every ordered-product logarithm coordinate is weighted
homogeneous for the positive Borel root heights. -/
theorem BorelRootProductPolynomialEquiv.exists_positive_weights
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val) :
    ∃ d : borelRootCharacterIndex J π → ℕ, (∀ j, 0 < d j) ∧
      ∀ (l : List (borelRootCharacterIndex J π)) (i : borelRootCharacterIndex J π)
        (m : borelRootCharacterIndex J π →₀ ℕ),
        m ∈ (borelRootProductLogarithm J hJ π hπ x l (e.coord i)).support →
          m.weight d = d i := by
  obtain ⟨d, hd, hrel⟩ :=
    BorelRootCharacterHeights.exists_positive_degrees I J hJI hI hJ π hπ hker hB
  exact ⟨d, hd, fun l i m hm => hrel m i
    (BorelRootProductLogarithm.support_character I J hJI hI hJ π hπ hker hB
      x e he hx l i m hm)⟩

omit [Finite ι] in
/-- For a duplicate-free list containing every Borel root
character, the linear part of the ordered-product logarithm is the
identity in the dual root coordinates. -/
theorem BorelRootProductLogarithm.coeff_single_basis
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    [DecidableEq (borelRootCharacterIndex J π)]
    (l : List (borelRootCharacterIndex J π)) (hl : l.Nodup) (hall : ∀ j, j ∈ l)
    (i j : borelRootCharacterIndex J π) :
    (borelRootProductLogarithm J hJ π hπ x l (e.coord i)).coeff
        (Finsupp.single j 1) = if i = j then 1 else 0 := by
  have hxU (k) : gaAffineGroupTangent (x k) ∈ rootTangentSpace J π hπ :=
    he k ▸ (e k).property
  rw [BorelRootProductLogarithm.coeff_single_of_nodup J hJ π hπ x hxU l hl j (hall j)]
  have hej : (⟨gaAffineGroupTangent (x j), hxU j⟩ : rootTangentSpace J π hπ) = e j :=
    Subtype.ext (he j).symm
  rw [hej, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-- **Polynomial inversion of the ordered root product.** For the
original root tangent basis and every duplicate-free list containing every
original Borel root character, there is a polynomial algebra automorphism
whose generator images are exactly the ordered-product logarithm
coordinates. It is the positive-weight triangular inverse of
`Geometry/PositiveWeightTriangularity.lean`, with weights
the positive root heights for the base selected by the original Borel. -/
theorem BorelRootProductPolynomialEquiv.exists_polynomialEquiv
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    (l : List (borelRootCharacterIndex J π)) (hl : l.Nodup) (hall : ∀ j, j ∈ l) :
    ∃ F : MvPolynomial (borelRootCharacterIndex J π) K ≃ₐ[K]
        MvPolynomial (borelRootCharacterIndex J π) K,
      ∀ i, F (X i) = borelRootProductLogarithm J hJ π hπ x l (e.coord i) := by
  classical
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  let _ : Fintype (borelRootCharacterIndex J π) := Fintype.ofFinite _
  obtain ⟨d, hd, hw⟩ := BorelRootProductPolynomialEquiv.exists_positive_weights
    I J hJI hI hJ π hπ hker hB x e he hx
  let p := fun i => borelRootProductLogarithm J hJ π hπ x l (e.coord i)
  exact ⟨positiveWeightPolynomialAlgEquiv d hd p (fun i m hm => hw l i m hm)
      (BorelRootProductLogarithm.coeff_single_basis J hJ π hπ x e he l hl hall),
    fun i => positiveWeightPolynomialAlgEquiv_X _ _ _ _ _ i⟩

end ReductiveGroups
