import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubset
import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialAdditivity

/-!
# Borel Root Closed Subset Group

For a closed set of Borel root characters, `U_S` is a subgroup
of the K-points of the original Ga-only Borel subgroup. A decomposition of a
closed set into two disjoint closed sets gives unique factorization
`U_S = U_{S₁} U_{S₂}`. -/

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

omit [Finite ι] in
/-- The equality is

```lean
(borelRootUnipotentExponentialEquiv J hJ π hπ).symm 1 = 0
```
-/
theorem BorelRootUnipotentExponentialEquiv.symm_one
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) :
    (borelRootUnipotentExponentialEquiv J hJ π hπ).symm 1 = 0 := by
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  exact (borelRootUnipotentExponential_zero J hJ π hπ).symm

omit [Finite ι] in
/-- The equality is

```lean
(borelRootUnipotentExponentialEquiv J hJ π hπ).symm g⁻¹ =
      -(borelRootUnipotentExponentialEquiv J hJ π hπ).symm g
```
-/
theorem BorelRootUnipotentExponentialEquiv.symm_inv
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : borelRootUnipotentPoints J π hπ) :
    (borelRootUnipotentExponentialEquiv J hJ π hπ).symm g⁻¹ =
      -(borelRootUnipotentExponentialEquiv J hJ π hπ).symm g := by
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  change _ = borelRootUnipotentExponential J hJ π hπ _
  rw [borelRootUnipotentExponential_neg]
  have h := congrArg Subtype.val
    ((borelRootUnipotentExponentialEquiv J hJ π hπ).apply_symm_apply g)
  change borelRootUnipotentExponential J hJ π hπ _ = _ at h
  rw [h]
  rfl

/-- For a closed set `S` of Borel root characters, `U_S` is a
subgroup of the K-points of the original Ga-only Borel subgroup. -/
def borelRootSubsetSubgroup
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
    (S : Set (borelRootCharacterIndex J π)) (hS : IsBorelRootCharacterClosed J π S) :
    Subgroup (borelRootUnipotentPoints J π hπ) where
  carrier := borelRootSubsetPoints J hJ π hπ e S
  one_mem' := by
    intro i _
    change e.coord i ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm 1) = 0
    rw [BorelRootUnipotentExponentialEquiv.symm_one, map_zero]
  inv_mem' := by
    intro g hg i hi
    change e.coord i ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g⁻¹) = 0
    rw [BorelRootUnipotentExponentialEquiv.symm_inv, map_neg, hg i hi, neg_zero]
  mul_mem' := by
    classical
    intro g h hg hh
    let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
    let _ : Fintype S := Fintype.ofFinite _
    have hxU (k) : gaAffineGroupTangent (x k) ∈ rootTangentSpace J π hπ :=
      he k ▸ (e k).property
    have hew (i) : (e i).val ∈ affineGroupCharacterWeightSpace π i.val := by
      rw [he]; exact hx i
    let l : List S := (Finset.univ : Finset S).toList
    have hl : l.Nodup := Finset.nodup_toList _
    have hall : ∀ j, j ∈ l := fun j => Finset.mem_toList.mpr (Finset.mem_univ j)
    obtain ⟨a, rfl⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
      x e he hx hxU hS l hl hall g hg
    obtain ⟨b, rfl⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
      x e he hx hxU hS l hl hall h hh
    let y : S ⊕ S → B →ₐc[K] SymmetricAlgebra K K := fun k => x (Sum.elim Subtype.val Subtype.val k)
    let r : S ⊕ S → borelRootCharacterIndex J π := Sum.elim Subtype.val Subtype.val
    have hmem := borelRootProduct_mem_subsetPoints I J hJI hI hJ π hπ hker hB e hew hS
      y r (fun k => by cases k <;> exact Subtype.property _)
      (fun k => hx (r k)) (fun k => hxU (r k))
      (l.map Sum.inl ++ l.map Sum.inr) (Sum.elim a b)
    convert hmem using 1
    apply Subtype.ext
    simp only [borelRootSubsetProduct, Subgroup.coe_mul, List.map_append, List.map_map,
      List.prod_append]
    rfl

omit [Finite ι] in
/-- Ordered `S`-products lie in `U_S` when `S` is closed. -/
theorem borelRootSubsetProduct_mem
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    [Finite ι]
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ))
    (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    (hxU : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    {S : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    (l : List S) (a : S → K) :
    borelRootSubsetProduct J π hπ x hxU S l a ∈ borelRootSubsetPoints J hJ π hπ e S := by
  classical
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  let _ : Fintype S := Fintype.ofFinite _
  have hew (i) : (e i).val ∈ affineGroupCharacterWeightSpace π i.val := by
    rw [he]; exact hx i
  exact borelRootProduct_mem_subsetPoints I J hJI hI hJ π hπ hker hB e hew hS
    (fun j : S => x j.val) (fun j => j.val) (fun j => j.property) (fun j => hx j.val)
    (fun j => hxU j.val) l a

/-- **Unique factorization.** If a closed set `S` of Borel root characters
is the disjoint union of closed sets `S₁` and `S₂`, every point of `U_S`
factors uniquely as `g₁ g₂` with `g₁ ∈ U_{S₁}` and `g₂ ∈ U_{S₂}`. -/
theorem borelRootSubsetPoints_existsUnique_mul
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
    {S S₁ S₂ : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    (hS₁ : IsBorelRootCharacterClosed J π S₁) (hS₂ : IsBorelRootCharacterClosed J π S₂)
    (hunion : S = S₁ ∪ S₂) (hdisj : Disjoint S₁ S₂)
    (g : borelRootUnipotentPoints J π hπ) (hg : g ∈ borelRootSubsetPoints J hJ π hπ e S) :
    ∃! p : borelRootUnipotentPoints J π hπ × borelRootUnipotentPoints J π hπ,
      p.1 ∈ borelRootSubsetPoints J hJ π hπ e S₁ ∧
      p.2 ∈ borelRootSubsetPoints J hJ π hπ e S₂ ∧ p.1 * p.2 = g := by
  classical
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  have hxU (k) : gaAffineGroupTangent (x k) ∈ rootTangentSpace J π hπ :=
    he k ▸ (e k).property
  let _ : Fintype S₁ := Fintype.ofFinite _
  let _ : Fintype S₂ := Fintype.ofFinite _
  let l₁ : List S₁ := (Finset.univ : Finset S₁).toList
  let l₂ : List S₂ := (Finset.univ : Finset S₂).toList
  have hl₁ : l₁.Nodup := Finset.nodup_toList _
  have hl₂ : l₂.Nodup := Finset.nodup_toList _
  have hall₁ : ∀ j, j ∈ l₁ := fun j => Finset.mem_toList.mpr (Finset.mem_univ j)
  have hall₂ : ∀ j, j ∈ l₂ := fun j => Finset.mem_toList.mpr (Finset.mem_univ j)
  let ι₁ : S₁ → S := fun j => ⟨j.val, hunion ▸ Or.inl j.property⟩
  let ι₂ : S₂ → S := fun j => ⟨j.val, hunion ▸ Or.inr j.property⟩
  have hι₁ : Function.Injective ι₁ := fun a b h =>
    Subtype.ext (Subtype.ext_iff.mp h :)
  have hι₂ : Function.Injective ι₂ := fun a b h =>
    Subtype.ext (Subtype.ext_iff.mp h :)
  let L : List S := l₁.map ι₁ ++ l₂.map ι₂
  have hL : L.Nodup := by
    refine List.nodup_append.mpr ⟨hl₁.map hι₁, hl₂.map hι₂, ?_⟩
    intro a ha b hb hab
    obtain ⟨a', -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', -, rfl⟩ := List.mem_map.mp hb
    have hv : a'.val = b'.val := congrArg Subtype.val hab
    exact Set.disjoint_left.mp hdisj a'.property (hv ▸ b'.property)
  have hallL : ∀ j, j ∈ L := by
    intro j
    have hj : j.val ∈ S₁ ∪ S₂ := hunion ▸ j.property
    rcases hj with h | h
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨j.val, h⟩, hall₁ _, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨j.val, h⟩, hall₂ _, rfl⟩)
  have hsplit (a : S → K) :
      borelRootSubsetProduct J π hπ x hxU S L a =
        borelRootSubsetProduct J π hπ x hxU S₁ l₁ (a ∘ ι₁) *
          borelRootSubsetProduct J π hπ x hxU S₂ l₂ (a ∘ ι₂) := by
    apply Subtype.ext
    simp only [borelRootSubsetProduct, Subgroup.coe_mul, L, List.map_append, List.map_map,
      List.prod_append]
    rfl
  obtain ⟨a, rfl⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
    x e he hx hxU hS L hL hallL g hg
  refine ⟨(borelRootSubsetProduct J π hπ x hxU S₁ l₁ (a ∘ ι₁),
      borelRootSubsetProduct J π hπ x hxU S₂ l₂ (a ∘ ι₂)),
    ⟨borelRootSubsetProduct_mem I J hJI hI hJ π hπ hker hB x e he hx hxU hS₁ l₁ _,
      borelRootSubsetProduct_mem I J hJI hI hJ π hπ hker hB x e he hx hxU hS₂ l₂ _,
      (hsplit a).symm⟩, ?_⟩
  rintro ⟨g₁, g₂⟩ ⟨h₁, h₂, hprod⟩
  obtain ⟨b₁, rfl⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
    x e he hx hxU hS₁ l₁ hl₁ hall₁ g₁ h₁
  obtain ⟨b₂, rfl⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
    x e he hx hxU hS₂ l₂ hl₂ hall₂ g₂ h₂
  have hnot (j : S) (h : j.val ∉ S₁) : j.val ∈ S₂ := by
    have hj : j.val ∈ S₁ ∪ S₂ := hunion ▸ j.property
    exact hj.resolve_left h
  let a' : S → K := fun j => if h : j.val ∈ S₁ then b₁ ⟨j.val, h⟩ else b₂ ⟨j.val, hnot j h⟩
  have ha'₁ : a' ∘ ι₁ = b₁ := by
    funext j
    simp [a', ι₁, j.property]
  have ha'₂ : a' ∘ ι₂ = b₂ := by
    funext j
    have hj : j.val ∉ S₁ := fun h => Set.disjoint_left.mp hdisj h j.property
    simp [a', ι₂, hj]
  have heq : a' = a := by
    apply borelRootSubsetProduct_injective I J hJI hI hJ π hπ hker hB x e he hx hxU
      S L hL hallL
    rw [hsplit a', ha'₁, ha'₂]
    exact hprod
  subst heq
  rw [ha'₁, ha'₂]

end ReductiveGroups
