import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSystemBridge
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues

/-!
# Borel Root Pair Independence

Distinct positive roots of a reduced root system are linearly independent;
consequently two distinct original Borel root characters are linearly
independent in the character lattice, and the original torus points take
arbitrary independent nonzero values on them. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

section RootPairing

variable {ι₀ R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι₀ R M₀ N₀} [P.IsReduced]

/-- Two distinct positive roots of a reduced root pairing are linearly
independent. -/
theorem linearIndependent_pair_of_isPos (b : P.Base) {i j : ι₀}
    (hi : b.IsPos i) (hj : b.IsPos j) (hij : i ≠ j) :
    LinearIndependent R ![P.root i, P.root j] := by
  by_contra h
  rcases RootPairing.IsReduced.eq_or_eq_neg i j h with he | he
  · exact hij (P.root.injective he)
  · have hneg : P.root (P.reflectionPerm j j) = P.root i := by
      rw [P.root_reflectionPerm, P.reflection_apply_self, he]
    have hij' : P.reflectionPerm j j = i := P.root.injective hneg
    have := (isPos_neg_index_iff b j).mp (hij' ▸ hi)
    exact this hj

end RootPairing

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Character differentials on the torus tangent image, as an additive map
on the character lattice. -/
def characterDifferentialOnImageHom (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :
    (ι →₀ ℤ) →+ (diagonalizableTangentImage π →ₗ[K] K) where
  toFun a := characterDifferentialOnImage π hπ (Multiplicative.ofAdd a)
  map_zero' := characterDifferentialOnImage_one π hπ
  map_add' a b := by
    simp only [ofAdd_add, characterDifferentialOnImage, characterDifferential_mul,
      LinearMap.add_comp]

/-- Two distinct Borel root characters are linearly independent
over `ℤ` in the character lattice. -/
theorem BorelRootCharacter.pair_linearIndependent
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    {τ β : borelRootCharacterIndex J π} (hτβ : τ ≠ β) :
    LinearIndependent ℤ ![Multiplicative.toAdd τ.val, Multiplicative.toAdd β.val] := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let P := rootSystem (centerQuotientCartan H)
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  let r : borelRootCharacterIndex J π → (centerQuotientCartan H).root :=
    fun j => E (borelRootCharacterOccurring J π j)
  let b := borelRootBase I J hJI hI hJ π hπ hker hB
  have hr (j : borelRootCharacterIndex J π) (t : H) :
      P.root (r j) (centerQuotientCartanMap H t) =
        characterDifferentialOnImage π hπ j.val t :=
    ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB
      (borelRootCharacterOccurring J π j) t
  have hne : r τ ≠ r β := by
    intro h
    apply hτβ
    have := congrArg Subtype.val (E.injective h)
    exact Subtype.ext this
  have hind := linearIndependent_pair_of_isPos b
    (borelRootBase_isPos I J hJI hI hJ π hπ hker hB τ)
    (borelRootBase_isPos I J hJI hI hJ π hπ hker hB β) hne
  rw [LinearIndependent.pair_iff] at hind ⊢
  intro s t hst
  have happ : s • characterDifferentialOnImageHom π hπ (Multiplicative.toAdd τ.val) +
      t • characterDifferentialOnImageHom π hπ (Multiplicative.toAdd β.val) = 0 := by
    rw [← map_zsmul (characterDifferentialOnImageHom π hπ),
      ← map_zsmul (characterDifferentialOnImageHom π hπ), ← map_add, hst, map_zero]
  have hK : ((s : K) • P.root (r τ) + (t : K) • P.root (r β)) = 0 := by
    ext h
    obtain ⟨u, rfl⟩ := centerQuotientCartanMap_surjective H h
    have hu := LinearMap.congr_fun happ u
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at hu ⊢
    rw [hr, hr]
    change s • characterDifferentialOnImage π hπ τ.val u +
      t • characterDifferentialOnImage π hπ β.val u = 0 at hu
    simpa only [zsmul_eq_mul, smul_eq_mul] using hu
  obtain ⟨hs, ht⟩ := hind s t hK
  exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩

/-- The torus points take arbitrary nonzero values on two distinct
Borel root characters simultaneously. -/
theorem exists_torusPoint_pair_values
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    {τ β : borelRootCharacterIndex J π} (hτβ : τ ≠ β) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      t.ofConv (MonoidAlgebra.single τ.val 1) = u ∧
        t.ofConv (MonoidAlgebra.single β.val 1) = v := by
  have hlin := BorelRootCharacter.pair_linearIndependent I J hJI hI hJ π hπ hker hB hτβ
  have hlin' : LinearIndependent ℤ
      (fun s : Fin 2 => Multiplicative.toAdd ((![τ.val, β.val] : Fin 2 → M) s)) := by
    convert hlin using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨t, ht⟩ := exists_torusPoint_character_values (K := K) (![τ.val, β.val] : Fin 2 → M)
    hlin' ![Units.mk0 u hu, Units.mk0 v hv]
  refine ⟨t, ?_, ?_⟩
  · have h0 := ht 0
    simp only [Matrix.cons_val_zero, Units.val_mk0] at h0
    exact h0
  · have h1 := ht 1
    simp only [Matrix.cons_val_one] at h1
    exact h1

end ReductiveGroups
