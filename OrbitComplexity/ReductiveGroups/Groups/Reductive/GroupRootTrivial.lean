import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates

/-!
# Triviality of a closed positive-root subgroup

Polynomial coordinate evaluations distinguish two rational points when the root
support is nonempty. An empty support has a constant coordinate algebra.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A closed positive-root subgroup is trivial exactly when its root support is empty. -/
theorem rootSubsetPoints_eq_bot_iff (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (hpos : ∀ r ∈ R, G.rootBase.IsPos r) :
    G.rootSubsetPoints R hR = ⊥ ↔ R = ∅ := by
  let A := G.rootSubsetAlgebra R hR
  let e := G.rootSubsetCoordinateEquiv R hR
  let f := CommHopfAlgCat.quotientPointsHom (CommHopfAlgCat.of K G.coordinateAlgebra)
    (G.rootSubsetIdeal R hR) (CommAlgCat.of K K)
  constructor
  · intro hbot
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    let i : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} := ⟨r, hpos r hr, hr⟩
    let p₀ : A →ₐ[K] K := (MvPolynomial.aeval fun _ => (0 : K)).comp e.toAlgHom
    let p₁ : A →ₐ[K] K := (MvPolynomial.aeval fun _ => (1 : K)).comp e.toAlgHom
    have h₀ : f (WithConv.toConv p₀) ∈ G.rootSubsetPoints R hR := ⟨_, rfl⟩
    have h₁ : f (WithConv.toConv p₁) ∈ G.rootSubsetPoints R hR := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h₀ h₁
    have hp : p₀ = p₁ := congrArg WithConv.ofConv
      (CommHopfAlgCat.quotientPointsHom_injective _ _ _ (h₀.trans h₁.symm))
    have hz := congrArg (fun p : A →ₐ[K] K => p (e.symm (MvPolynomial.X i))) hp
    have hzero : (0 : K) = 1 := by
      simpa only [p₀, p₁, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        AlgEquiv.apply_symm_apply, MvPolynomial.aeval_X] using hz
    exact zero_ne_one hzero
  · intro hempty
    apply le_antisymm ?_ bot_le
    intro g hg
    change ∃ p, f p = g at hg
    obtain ⟨p, rfl⟩ := hg
    let : IsEmpty {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} :=
      ⟨fun r => (hempty ▸ r.property.2 : r.val ∈ (∅ : Set G.rootIndex))⟩
    have hp : p.ofConv.comp e.symm.toAlgHom =
        (1 : WithConv (A →ₐ[K] K)).ofConv.comp e.symm.toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      exact isEmptyElim i
    have hpone : p = 1 := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro a
      have h := congrArg (fun z => z (e a)) hp
      change p.ofConv (e.symm (e a)) =
        (1 : WithConv (A →ₐ[K] K)).ofConv (e.symm (e a)) at h
      have hea : e.symm (e a) = a := e.symm_apply_apply a
      exact (congrArg p.ofConv hea).symm.trans
        (h.trans (congrArg (1 : WithConv (A →ₐ[K] K)).ofConv hea))
    rw [Subgroup.mem_bot, hpone]
    exact map_one f.hom

end ReductiveGroups.ReductiveGroupData
