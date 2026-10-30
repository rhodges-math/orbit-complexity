import OrbitComplexity.GroupActions.Varieties.Dimension
import OrbitComplexity.GroupActions.Varieties.Noetherian
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # Finiteness of dimensions

A finite affine cover bounds the dimension of a variety by the dimensions of finitely many
coordinate rings. Finite type algebras over a field have finite Krull dimension.

## Main results

* `GroupActions.Variety.dim_ne_top`: a variety has finite Krull dimension.
* `GroupActions.Variety.dim_nonneg`: a nonempty variety has nonnegative dimension.
* `GroupActions.Variety.subsetDim_ne_top`: sets of rational points have finite dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

universe u

/-- Taking the natural value of a finite non-bottom extended dimension preserves that dimension. -/
theorem natCast_unbotD_toNat (d : WithBot ℕ∞) (hbot : d ≠ ⊥) (htop : d ≠ ⊤) :
    (((d.unbotD 0).toNat : ℕ) : WithBot ℕ∞) = d := by
  let n : ℕ∞ := d.unbot hbot
  have hn : (n : WithBot ℕ∞) = d := WithBot.coe_unbot d hbot
  have hntop : n ≠ ⊤ := by
    intro h
    apply htop
    rw [← hn, h, WithBot.coe_top]
  rw [← hn, WithBot.unbotD_coe]
  exact congrArg (fun a : ℕ∞ ↦ (a : WithBot ℕ∞)) (ENat.natCast_toNat hntop)

private theorem affine_dim_ne_top (K : Type u) [Field K] (V : Scheme.{u}) [IsAffine V]
    (f : V ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    topologicalKrullDim V ≠ ⊤ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.isoSpec.inv ≫ f)
  let : Algebra K Γ(V, ⊤) := φ.hom.toAlgebra
  have : Algebra.FiniteType K Γ(V, ⊤) := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp
    rw [hφ]
    infer_instance
  have hdim : topologicalKrullDim V = ringKrullDim Γ(V, ⊤) :=
    V.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
  rw [hdim]
  cases subsingleton_or_nontrivial Γ(V, ⊤) with
  | inl h =>
    have : Subsingleton Γ(V, ⊤) := h
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_ne_top
  | inr h =>
    have : Nontrivial Γ(V, ⊤) := h
    have := TauCeti.finiteRingKrullDim_of_finiteType K Γ(V, ⊤)
    exact ringKrullDim_ne_top

variable {K : Type u} [Field K] (X : GroupActions.Variety K)

/-- A variety over a field has finite Krull dimension. -/
theorem dim_ne_top : X.dim ≠ ⊤ := by
  let U := X.scheme.affineCover.finiteSubcover
  rw [dim, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_iSup_openCover U]
  apply iSup_ne_top
  intro i
  have : IsAffine (U.X i) := by
    dsimp [U, Scheme.OpenCover.finiteSubcover]
    infer_instance
  exact affine_dim_ne_top K (U.X i) (U.f i ≫ X.toSpec)

/-- A nonempty variety has nonnegative Krull dimension. -/
theorem dim_nonneg [Nonempty X.scheme] : 0 ≤ X.dim := by
  obtain ⟨x⟩ : Nonempty X.scheme := inferInstance
  have : Nonempty (IrreducibleCloseds X.scheme) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- A nonempty variety has dimension different from bottom. -/
theorem dim_ne_bot [Nonempty X.scheme] : X.dim ≠ ⊥ := by
  intro h
  exact not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) (h ▸ X.dim_nonneg)

/-- The natural dimension of a finite type variety, assigning zero to the empty scheme. -/
noncomputable def natDim : ℕ := (X.dim.unbotD 0).toNat

/-- The natural dimension of a nonempty variety equals its Krull dimension after casting. -/
theorem natDim_cast [Nonempty X.scheme] : (X.natDim : WithBot ℕ∞) = X.dim :=
  natCast_unbotD_toNat X.dim X.dim_ne_bot X.dim_ne_top

/-- A set of rational points has finite dimension. -/
theorem subsetDim_ne_top (S : Set X.points) : X.subsetDim S ≠ ⊤ := by
  intro h
  apply X.dim_ne_top
  exact top_le_iff.mp (h ▸ X.subsetDim_le S)

/-- A nonempty set of rational points has nonnegative dimension. -/
theorem subsetDim_nonneg {S : Set X.points} (hS : S.Nonempty) : 0 ≤ X.subsetDim S := by
  obtain ⟨x, hx⟩ := hS
  let y : X.pointClosure S := ⟨X.pointMap x, subset_closure ⟨x, hx, rfl⟩⟩
  have : Nonempty (IrreducibleCloseds (X.pointClosure S)) :=
    ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

end GroupActions.Variety
