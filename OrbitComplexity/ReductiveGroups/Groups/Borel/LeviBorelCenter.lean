import OrbitComplexity.ReductiveGroups.Groups.Borel.LeviBorelUnipotent

/-!
# Levi Borel Center

The central diagonalizable subgroup `Z_I` of the standard Levi subgroup, on characters:
Borel root characters in `Φ_I^+` are trivial on `Z_I`, and every other Borel
root character takes the value `2` at some point of `Z_I`. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
/-- The equality is

```lean
characterDifferentialOnImage π hπ (a * b) =
      characterDifferentialOnImage π hπ a + characterDifferentialOnImage π hπ b
```
-/
theorem characterDifferentialOnImage_mul'
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (a b : Multiplicative (ι →₀ ℤ)) :
    characterDifferentialOnImage π hπ (a * b) =
      characterDifferentialOnImage π hπ a + characterDifferentialOnImage π hπ b := by
  simp only [characterDifferentialOnImage, characterDifferential_mul, LinearMap.add_comp]

/-- A Borel root character in `Φ_I^+` is trivial on `Z_I`. -/
theorem leviBorelRootSet_character_eq_one
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (Isimple : Set (borelRootBase I J hJI hI hJ π hπ hker hB).support)
    (k : borelRootCharacterIndex J π)
    (hk : k ∈ leviBorelRootSet I J hJI hI hJ π hπ hker hB Isimple)
    (t : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K))
    (ht : ∀ j ∈ Isimple, t.ofConv (MonoidAlgebra.single
      (rootCharacter I hI π hπ hker hB j.val) 1) = 1) :
    t.ofConv (MonoidAlgebra.single k.val 1) = 1 := by
  classical
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let P := rootSystem (centerQuotientCartan H)
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  obtain ⟨l, hl, hsum⟩ := exists_root_list_of_mem_closure_image hk.2
  let χ : (centerQuotientCartan H).root → Multiplicative (ι →₀ ℤ) :=
    rootCharacter I hI π hπ hker hB
  have hroot (γ : (centerQuotientCartan H).root) (u : H) :
      characterDifferentialOnImage π hπ (χ γ) u = P.root γ (centerQuotientCartanMap H u) := by
    have h := ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB
      (E.symm γ) u
    rw [E.apply_symm_apply] at h
    exact h.symm
  have hlist : ∀ l' : List (centerQuotientCartan H).root, ∀ u : H,
      characterDifferentialOnImage π hπ (l'.map χ).prod u =
        (l'.map P.root).sum (centerQuotientCartanMap H u) := by
    intro l' u
    induction l' with
    | nil => simp [characterDifferentialOnImage_one]
    | cons γ l' ih =>
      have e1 : (List.map χ (γ :: l')).prod = χ γ * (l'.map χ).prod := List.prod_cons
      have e2 : (List.map P.root (γ :: l')).sum = P.root γ + (l'.map P.root).sum :=
        List.sum_cons
      rw [e1, e2, characterDifferentialOnImage_mul']
      rw [LinearMap.add_apply]
      rw [LinearMap.add_apply]
      rw [ih]
      exact congrArg (· + _) (hroot γ u)
  have hchar : k.val = (l.map χ).prod := by
    apply characterDifferentialOnImage_injective π hπ
    ext u
    change characterDifferentialOnImage π hπ k.val u =
      characterDifferentialOnImage π hπ (l.map χ).prod u
    have hk' := ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB
      (borelRootCharacterOccurring J π k) u
    change P.root (E (borelRootCharacterOccurring J π k)) (centerQuotientCartanMap H u) =
      characterDifferentialOnImage π hπ k.val u at hk'
    exact hk'.symm.trans ((congrArg (fun v => v (centerQuotientCartanMap H u)) hsum.symm).trans
      (hlist l u).symm)
  let φ : Multiplicative (ι →₀ ℤ) →* K := t.ofConv.toMonoidHom.comp (MonoidAlgebra.of K _)
  change φ k.val = 1
  rw [hchar, map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro c hc
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hc
  obtain ⟨j, hj, rfl⟩ := hl γ hγ
  exact ht j hj

/-- For a Borel root character outside `Φ_I^+` there is a torus point that is
trivial on the simple roots of `I` and takes the value `2` on it. -/
theorem exists_leviCenter_character_two
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (Isimple : Set (borelRootBase I J hJI hI hJ π hπ hker hB).support)
    (k : borelRootCharacterIndex J π)
    (hk : k ∉ leviBorelRootSet I J hJI hI hJ π hπ hker hB Isimple) :
    ∃ t : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K),
      (∀ j ∈ Isimple, t.ofConv (MonoidAlgebra.single
        (rootCharacter I hI π hπ hker hB j.val) 1) = 1) ∧
      t.ofConv (MonoidAlgebra.single k.val 1) = 2 := by
  classical
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let P := rootSystem (centerQuotientCartan H)
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  let b := borelRootBase I J hJI hI hJ π hπ hker hB
  let γ := E (borelRootCharacterOccurring J π k)
  have hγ : b.IsPos γ := borelRootBase_isPos I J hJI hI hJ π hπ hker hB k
  have hind := LinearIndependent.option_of_notMem_leviPositiveRoots b Isimple hγ hk
  let α : Option Isimple → {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1} := fun o =>
    Option.casesOn' o (borelRootCharacterOccurring J π k) (fun j => E.symm j.val.val)
  have hroots : (fun o => P.root (E (α o))) =
      (fun o : Option Isimple => Option.casesOn' o (P.root γ)
        (fun j : Isimple => P.root j.val.val)) := by
    funext o
    cases o with
    | none => rfl
    | some j => simp [α, E.apply_symm_apply]
  have hlin := OccurringCharacter.family_linearIndependent I hI π hπ hker hB α
    (by rw [hroots]; exact hind)
  obtain ⟨t, ht⟩ := exists_torusPoint_character_values (K := K) (fun o => (α o).val) hlin
    (fun o => Option.casesOn' o (Units.mk0 (2 : K) two_ne_zero) (fun _ => 1))
  refine ⟨t, fun j hj => ?_, ?_⟩
  · have h := ht (some ⟨j, hj⟩)
    simp only [Option.casesOn', Units.val_one] at h
    exact h
  · have h := ht none
    simp only [Option.casesOn', Units.val_mk0] at h
    exact h

end ReductiveGroups
