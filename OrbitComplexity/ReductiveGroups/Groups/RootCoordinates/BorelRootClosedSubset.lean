import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductSupport
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCharacterHeights
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductLinearCoefficients

/-!
# Borel Root Closed Subset

Root subgroups attached to closed sets of Borel root characters.

A set `S` of Borel root characters is closed when every Borel root
character that is a monomial in characters from `S` already lies in `S`
(nonnegative integral combinations, as in nonnegative integral closures). For closed
`S`, the K-points `U_S` of the original Ga-only Borel subgroup whose
logarithm has dual root coordinates supported on `S` are exactly the ordered
products of the root Ga points indexed by `S`, in any order, with unique
parameters. -/

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

/-- K-points of the original Ga-only Borel subgroup. -/
abbrev borelRootUnipotentPoints (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)

/-- Closedness of a set of Borel root characters: a Borel root
character that is a monomial (nonnegative exponents) in characters of `S`
lies in `S`. -/
def IsBorelRootCharacterClosed (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (S : Set (borelRootCharacterIndex J π)) : Prop :=
  ∀ (m : borelRootCharacterIndex J π →₀ ℕ) (i : borelRootCharacterIndex J π),
    (↑m.support : Set _) ⊆ S → (m.prod fun j n => j.val ^ n) = i.val → i ∈ S

omit [IsAlgClosed K] [CharZero K] [Finite ι] in
/-- The equality is

```lean
((m.mapDomain r).prod fun j n => j.val ^ n) = m.prod fun k n => (r k).val ^ n
```
-/
theorem borelRootCharacter_prod_mapDomain
    {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    {κ : Type*} (r : κ → borelRootCharacterIndex J π) (m : κ →₀ ℕ) :
    ((m.mapDomain r).prod fun j n => j.val ^ n) = m.prod fun k n => (r k).val ^ n := by
  classical
  exact Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

omit [IsAlgClosed K] [CharZero K] [Finite ι] in
/-- Closedness applied to a monomial relation among characters indexed by
any family with values in `S`. -/
theorem IsBorelRootCharacterClosed.mem_of_prod
    {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    {S : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    {κ : Type*} (r : κ → borelRootCharacterIndex J π) (hr : ∀ k, r k ∈ S)
    (m : κ →₀ ℕ) (i : borelRootCharacterIndex J π)
    (h : (m.prod fun k n => (r k).val ^ n) = i.val) : i ∈ S := by
  classical
  apply hS (m.mapDomain r) i
  · intro j hj
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hj)
    exact hr k
  · rw [borelRootCharacter_prod_mapDomain, h]

/-- The points `U_S`: K-points of the original Ga-only Borel subgroup whose
logarithm has vanishing dual root coordinates outside `S`. -/
def borelRootSubsetPoints (J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (S : Set (borelRootCharacterIndex J π)) : Set (borelRootUnipotentPoints J π hπ) :=
  {g | ∀ i ∉ S, e.coord i ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g) = 0}

/-- **Support control for closed sets.** Every ordered product (repetitions
allowed) of weight Ga points whose characters lie in a closed set
`S` belongs to `U_S`. -/
theorem borelRootProduct_mem_subsetPoints
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
    (r : κ → borelRootCharacterIndex J π) (hr : ∀ k, r k ∈ S)
    (hy : ∀ k, gaAffineGroupTangent (y k) ∈ affineGroupCharacterWeightSpace π (r k).val)
    (hyU : ∀ k, gaAffineGroupTangent (y k) ∈ rootTangentSpace J π hπ)
    (l : List κ) (a : κ → K) :
    (⟨(l.map (fun k => gaParameterPoint (y k) (a k))).prod,
        GaParameterPoint.prod_mem_of_tangent_mem_quotient y
          (borelRootUnipotentHopfIdeal J π hπ) hyU l a⟩ :
      borelRootUnipotentPoints J π hπ) ∈ borelRootSubsetPoints J hJ π hπ e S := by
  intro i hi
  exact BorelRootProduct.logarithm_coord_eq_zero_of_not_monomial I J hJI hI hJ π hπ hker hB
    e he y (fun k => (r k).val) hy hyU l i
    (fun m hm => hi (hS.mem_of_prod r hr m i hm)) a

/-- The ordered product of the chosen root Ga points indexed by a list of
elements of `S`, as a point of the original Ga-only Borel subgroup. -/
def borelRootSubsetProduct (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (hxU : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (S : Set (borelRootCharacterIndex J π)) (l : List S) (a : S → K) :
    borelRootUnipotentPoints J π hπ :=
  ⟨_, GaParameterPoint.prod_mem_of_tangent_mem_quotient (fun j : S => x j.val)
      (borelRootUnipotentHopfIdeal J π hπ) (fun j => hxU j.val) l a⟩

/-- For any set `S` and a duplicate-free list of all its elements, the
logarithm coordinates of the ordered `S`-product, indexed by `S`, are the
generator images of a polynomial automorphism (positive root heights, identity
linear part). -/
theorem exists_borelRootSubset_polynomialEquiv
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
    (S : Set (borelRootCharacterIndex J π))
    (l : List S) (hl : l.Nodup) (hall : ∀ j, j ∈ l) :
    ∃ F : MvPolynomial S K ≃ₐ[K] MvPolynomial S K, ∀ i : S,
      F (X i) = borelRootProductLogarithm J hJ π hπ (fun j : S => x j.val) l
        (e.coord i.val) := by
  classical
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  let _ : Fintype S := Fintype.ofFinite _
  obtain ⟨d, hd, hrel⟩ :=
    BorelRootCharacterHeights.exists_positive_degrees I J hJI hI hJ π hπ hker hB
  have hxU (k) : gaAffineGroupTangent (x k) ∈ rootTangentSpace J π hπ :=
    he k ▸ (e k).property
  have hew (i) : (e i).val ∈ affineGroupCharacterWeightSpace π i.val := by
    rw [he]; exact hx i
  let p : S → MvPolynomial S K := fun i =>
    borelRootProductLogarithm J hJ π hπ (fun j : S => x j.val) l (e.coord i.val)
  have hw : ∀ i m, m ∈ (p i).support → m.weight (fun j : S => d j.val) = d i.val := by
    intro i m hm
    have hrelm := borelRootProductLogarithm_support_prod I J hJI hI hJ π hπ hker hB
      e hew (fun j : S => x j.val) (fun j => j.val.val) (fun j => hx j.val)
      (fun j => hxU j.val) l i.val m hm
    have h2 := hrel (m.mapDomain Subtype.val) i.val
      (by rw [borelRootCharacter_prod_mapDomain]; exact hrelm)
    rw [← h2, Finsupp.weight_apply, Finsupp.weight_apply,
      Finsupp.sum_mapDomain_index (h := fun i c => c • d i) (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
  have hlinear : ∀ i j, (p i).coeff (Finsupp.single j 1) = if i = j then 1 else 0 := by
    intro i j
    change (borelRootProductLogarithm J hJ π hπ (fun j : S => x j.val) l
      (e.coord i.val)).coeff (Finsupp.single j 1) = _
    rw [BorelRootProductLogarithm.coeff_single_of_nodup J hJ π hπ (fun j : S => x j.val)
      (fun j => hxU j.val) l hl j (hall j)]
    have hej : (⟨gaAffineGroupTangent (x j.val), hxU j.val⟩ :
        rootTangentSpace J π hπ) = e j.val := Subtype.ext (he j.val).symm
    rw [hej, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : j.val ≠ i.val := fun h => hij (Subtype.ext h).symm
      simp [hij, hne]
  exact ⟨positiveWeightPolynomialAlgEquiv (fun j : S => d j.val) (fun j => hd _) p hw hlinear,
    fun i => positiveWeightPolynomialAlgEquiv_X _ _ _ _ _ i⟩

/-- **The `S`-chart is onto `U_S`.** For closed `S` and any duplicate-free
list of its elements, every point of `U_S` is the ordered `S`-product for
some parameters. -/
theorem borelRootSubsetProduct_surjective
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
    (hxU : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    {S : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    (l : List S) (hl : l.Nodup) (hall : ∀ j, j ∈ l)
    (g : borelRootUnipotentPoints J π hπ) (hg : g ∈ borelRootSubsetPoints J hJ π hπ e S) :
    ∃ a : S → K, borelRootSubsetProduct J π hπ x hxU S l a = g := by
  classical
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  let _ : Fintype S := Fintype.ofFinite _
  have hew (i) : (e i).val ∈ affineGroupCharacterWeightSpace π i.val := by
    rw [he]; exact hx i
  obtain ⟨F, hF⟩ := exists_borelRootSubset_polynomialEquiv I J hJI hI hJ π hπ hker hB
    x e he hx S l hl hall
  let E := borelRootUnipotentExponentialEquiv J hJ π hπ
  let c : S → K := fun i => e.coord i.val (E.symm g)
  let a : S → K := fun j => MvPolynomial.aeval c (F.symm (X j))
  have hac : ∀ i : S, MvPolynomial.aeval a (F (X i)) = c i := by
    have h1 : (MvPolynomial.aeval c).comp F.symm.toAlgHom = MvPolynomial.aeval a := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [MvPolynomial.aeval_X]
      rfl
    intro i
    rw [← h1, AlgHom.comp_apply]
    change MvPolynomial.aeval c (F.symm (F (X i))) = c i
    rw [AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]
  refine ⟨a, ?_⟩
  apply E.symm.injective
  apply e.ext_elem
  intro i
  rw [← e.coord_apply, ← e.coord_apply]
  by_cases hi : i ∈ S
  · rw [borelRootSubsetProduct, ← borelRootProductLogarithm_eval J hJ π hπ (fun j : S => x j.val)
      (fun j => hxU j.val) l (e.coord i) a, ← hF ⟨i, hi⟩, hac ⟨i, hi⟩]
  · rw [hg i hi]
    exact borelRootProduct_mem_subsetPoints I J hJI hI hJ π hπ hker hB e hew hS
      (fun j : S => x j.val) (fun j => j.val) (fun j => j.property) (fun j => hx j.val)
      (fun j => hxU j.val) l a i hi

/-- **The `S`-chart is injective.** For any `S` and a duplicate-free list
of all its elements, the ordered `S`-product determines its parameters. -/
theorem borelRootSubsetProduct_injective
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
    (hxU : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (S : Set (borelRootCharacterIndex J π))
    (l : List S) (hl : l.Nodup) (hall : ∀ j, j ∈ l) :
    Function.Injective (borelRootSubsetProduct J π hπ x hxU S l) := by
  obtain ⟨F, hF⟩ := exists_borelRootSubset_polynomialEquiv I J hJI hI hJ π hπ hker hB
    x e he hx S l hl hall
  intro a a' h
  have hgen : (MvPolynomial.aeval a).comp F.toAlgHom =
      (MvPolynomial.aeval a').comp F.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change MvPolynomial.aeval a (F (X i)) = MvPolynomial.aeval a' (F (X i))
    rw [hF i, borelRootProductLogarithm_eval J hJ π hπ (fun j : S => x j.val)
      (fun j => hxU j.val) l (e.coord i.val) a,
      borelRootProductLogarithm_eval J hJ π hπ (fun j : S => x j.val)
      (fun j => hxU j.val) l (e.coord i.val) a']
    exact congrArg (fun g => e.coord i.val
      ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g)) h
  funext j
  have := DFunLike.congr_fun hgen (F.symm (X j))
  change MvPolynomial.aeval a (F (F.symm (X j))) =
    MvPolynomial.aeval a' (F (F.symm (X j))) at this
  rwa [AlgEquiv.apply_symm_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X] at this

end ReductiveGroups
