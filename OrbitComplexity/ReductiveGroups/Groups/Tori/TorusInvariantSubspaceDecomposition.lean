import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusInvariantSubspaceWeights
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Torus Invariant Subspace Decomposition

Invariant subspaces of a split-torus comodule: tangent weights
and point weights agree on a finite-dimensional representation. -/

noncomputable section
namespace ReductiveGroups

open TauCeti
open scoped TensorProduct

variable {K V ι : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Comodule K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) V]

local notation "M" => Multiplicative (ι →₀ ℤ)
local notation "T" => MonoidAlgebra K M

omit [CharZero K] [FiniteDimensional K V] in
/-- A tangent separating the finitely many occurring characters has exactly
those comodule weight spaces as eigenspaces. -/
theorem TorusTangentOperator.eigenspace_eq_weightSpace
    (s : Finset M)
    (hs : (⨆ α ∈ s, Comodule.weightSpace K M V α) = ⊤)
    (h : Derivation K T (Bialgebra.CounitAlgebra K T K))
    (hsep : Set.InjOn (fun α : M => characterDifferential (K := K) α h) s)
    (α : M) (hα : α ∈ s) :
    (torusTangentOperator h).eigenspace (characterDifferential α h) =
      Comodule.weightSpace K M V α := by
  let f : Module.End K V := torusTangentOperator h
  let W : s → Submodule K V := fun a => Comodule.weightSpace K M V a.val
  let E : s → Submodule K V := fun a =>
    f.eigenspace (characterDifferential (K := K) a.val h)
  have hWE (a : s) : W a ≤ E a := by
    intro v hv
    exact Module.End.mem_eigenspace_iff.mpr
      (torusTangentOperator_weight h a.val hv)
  have htop : (⨆ a : s, W a) = ⊤ := by
    apply top_unique
    rw [← hs]
    refine iSup₂_le fun a ha => ?_
    exact le_iSup_of_le (⟨a, ha⟩ : s) le_rfl
  have hsep' : Function.Injective
      (fun a : s => characterDifferential (K := K) a.val h) := by
    intro a b hab
    exact Subtype.ext (hsep a.property b.property hab)
  have hind : iSupIndep E :=
    (Module.End.eigenspaces_iSupIndep f).comp hsep'
  have heq : W = E := (hind.le_iff_eq_of_iSup_eq_top htop).mp hWE
  exact (congrFun heq (⟨α, hα⟩ : s)).symm

omit [CharZero K] in
/-- The finitely many nonzero weight spaces span a finite-dimensional split-torus comodule. -/
private theorem finite_weight_support_spans :
    ∃ s : Finset M, (⨆ α ∈ s, Comodule.weightSpace K M V α) = ⊤ := by
  classical
  let s : Finset M :=
    (Comodule.finite_setOf_weightSpace_ne_bot K M V).toFinset
  refine ⟨s, ?_⟩
  apply top_unique
  calc
    (⊤ : Submodule K V) = ⨆ α : M, Comodule.weightSpace K M V α :=
      (Comodule.iSup_weightSpace_eq_top K M V).symm
    _ ≤ ⨆ α ∈ s, Comodule.weightSpace K M V α := by
      refine iSup_le fun α => ?_
      by_cases hα : Comodule.weightSpace K M V α = ⊥
      · rw [hα]
        exact bot_le
      · have hmem : α ∈ s := by simpa [s] using hα
        exact le_iSup_of_le α (le_iSup_of_le hmem le_rfl)

/-- The torus point operator on the given comodule. -/
def torusPointOperator (g : T →ₐ[K] K) : Module.End K V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ
    (TensorProduct.map LinearMap.id g.toLinearMap) ∘ₗ
      Comodule.coact (R := K) (C := MonoidAlgebra K M)

omit [CharZero K] [FiniteDimensional K V] in
/-- The equality is

```lean
torusPointOperator g v = g (MonoidAlgebra.single α 1) • v
```
-/
theorem torusPointOperator_weight (g : T →ₐ[K] K) (α : M)
    {v : V} (hv : v ∈ Comodule.weightSpace K M V α) :
    torusPointOperator g v = g (MonoidAlgebra.single α 1) • v := by
  rw [torusPointOperator, LinearMap.comp_apply, LinearMap.comp_apply,
    Comodule.mem_weightSpace.mp hv]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.toLinearMap_apply]

/-- A subspace preserved by every tangent operator of a split torus is
preserved by every rational point of that torus. -/
theorem torusPointOperator_preserves_of_tangent
    (W : Submodule K V)
    (hW : ∀ h : Derivation K T (Bialgebra.CounitAlgebra K T K),
      ∀ v ∈ W, torusTangentOperator h v ∈ W)
    (g : T →ₐ[K] K) (v : V) (hv : v ∈ W) :
    torusPointOperator g v ∈ W := by
  classical
  obtain ⟨s, hs⟩ := finite_weight_support_spans (K := K) (V := V) (ι := ι)
  obtain ⟨h, hsep⟩ := exists_torusTangent_separating_finite (K := K) s
  let f : Module.End K V := torusTangentOperator h
  let p : Module.End K V := torusPointOperator g
  let eig : M → K := fun α => characterDifferential α h
  have hWE (α : M) : Comodule.weightSpace K M V α ≤ f.eigenspace (eig α) := by
    intro x hx
    exact Module.End.mem_eigenspace_iff.mpr (torusTangentOperator_weight h α hx)
  have hspan : (⨆ α ∈ s, f.eigenspace (eig α)) = ⊤ := by
    apply top_unique
    rw [← hs]
    exact iSup₂_mono fun α hα => hWE α
  have hall : (⨆ μ : K, f.eigenspace μ) = ⊤ := by
    apply top_unique
    rw [← hspan]
    refine iSup₂_le fun α _ => ?_
    exact le_iSup f.eigenspace (eig α)
  have hout (μ : K) (hμ : μ ∉ Set.range (fun a : s => eig a.val)) :
      f.eigenspace μ = ⊥ := by
    have hd := (Module.End.eigenspaces_iSupIndep f).disjoint_biSup hμ
    have hrange : (⨆ ξ ∈ Set.range (fun a : s => eig a.val), f.eigenspace ξ) = ⊤ := by
      apply top_unique
      rw [← hspan]
      refine iSup₂_le fun α hα => ?_
      exact le_iSup_of_le (eig α)
        (le_iSup_of_le ⟨⟨α, hα⟩, rfl⟩ le_rfl)
    rw [hrange, disjoint_top] at hd
    exact hd
  have hscalar (μ : K) (x : V) (hx : x ∈ f.eigenspace μ) :
      ∃ c : K, p x = c • x := by
    by_cases hμ : μ ∈ Set.range (fun a : s => eig a.val)
    · obtain ⟨a, rfl⟩ := hμ
      have hxa : x ∈ Comodule.weightSpace K M V a.val := by
        rw [← TorusTangentOperator.eigenspace_eq_weightSpace s hs h hsep
          a.val a.property]
        exact hx
      exact ⟨g (MonoidAlgebra.single a.val 1), torusPointOperator_weight g a.val hxa⟩
    · have hx0 : x = 0 := by
        have : x ∈ (⊥ : Submodule K V) := (hout μ hμ) ▸ hx
        simpa using this
      subst x
      exact ⟨0, by simp [p]⟩
  have hdecomp : W = ⨆ μ : K, W ⊓ f.eigenspace μ :=
    Submodule.eq_iSup_inf_genEigenspace (f := f) (k := 1) (hW h) hall
  have hpW : W ≤ W.comap p := by
    calc
      W = ⨆ μ : K, W ⊓ f.eigenspace μ := hdecomp
      _ ≤ W.comap p := by
        refine iSup_le fun μ => ?_
        intro x hx
        obtain ⟨c, hc⟩ := hscalar μ x hx.2
        change p x ∈ W
        rw [hc]
        exact W.smul_mem c hx.1
  exact hpW hv


end ReductiveGroups
