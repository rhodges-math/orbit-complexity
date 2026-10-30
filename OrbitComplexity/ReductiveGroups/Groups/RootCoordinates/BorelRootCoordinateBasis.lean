import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootTangentBasis
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Borel Root Coordinate Basis

Bases of the original Ga-only subgroup tangent, indexed by
the Borel characters and realized by Ga tangents. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u v
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CharZero K]

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

/-- A family spanning the original subgroup tangent gives a basis of
that very tangent space, with no replacement ambient vector space. -/
def borelRootTangentBasisOfSpan {κ : Type v}
    (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hli : LinearIndependent K (fun i => gaAffineGroupTangent (x i)))
    (hsp : Submodule.span K (Set.range (fun i => gaAffineGroupTangent (x i))) =
      (rootTangentSpace J π hπ).toSubmodule) :
    Module.Basis κ K (rootTangentSpace J π hπ) :=
  (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp)

/-- The equality is

```lean
(borelRootTangentBasisOfSpan J π hπ x hli hsp i).val =
      gaAffineGroupTangent (x i)
```
-/
@[simp] theorem borelRootTangentBasisOfSpan_val {κ : Type v}
    (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hli : LinearIndependent K (fun i => gaAffineGroupTangent (x i)))
    (hsp : Submodule.span K (Set.range (fun i => gaAffineGroupTangent (x i))) =
      (rootTangentSpace J π hπ).toSubmodule) (i : κ) :
    (borelRootTangentBasisOfSpan J π hπ x hli hsp i).val =
      gaAffineGroupTangent (x i) := by
  rw [borelRootTangentBasisOfSpan, Module.Basis.map_apply]
  exact Module.Basis.coe_span_apply hli i

/-- The Borel root generators have a character-indexed
basis, and their closed generated subgroup is the original Ga-only U. -/
theorem exists_borelRootCoordinateBasis [Finite ι]
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    ∃ (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
      (e : Module.Basis (borelRootCharacterIndex J π) K (rootTangentSpace J π hπ)),
      (∀ i, (e i).val = gaAffineGroupTangent (x i)) ∧
      (∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val) ∧
      gaGeneratedHopfIdeal x = borelRootUnipotentHopfIdeal J π hπ := by
  obtain ⟨x, hx, hli, hsp, hgen⟩ :=
    exists_borelRootGenerators_tangent_basis I J hJI hI hJ π hπ hker hB
  exact ⟨x, borelRootTangentBasisOfSpan J π hπ x hli hsp,
    borelRootTangentBasisOfSpan_val J π hπ x hli hsp,
    fun i => (hx i).2.1, hgen⟩

end ReductiveGroups
