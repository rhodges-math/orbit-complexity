import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme
import OrbitComplexity.FrobeniusSplitting.Splittings.Transport

/-!
# Direct images of Frobenius splittings

If the direct image of the structure sheaf along a morphism is isomorphic to its
target's structure sheaf, a splitting descends to the target.

## Main definitions

* `FrobeniusSplitting.SchemeSplitting.pushforward`: descent through the structure sheaf map.

## Main results

* `FrobeniusSplitting.SchemeSplitting.pushforward_app`: compatibility with the structure sheaf map.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Lemma 1.1.8.
-/

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry CategoryTheory Opposite

variable {X Y : Scheme} {p : ℕ}

/-- A splitting descends when the structure sheaf map to the direct image is an isomorphism. -/
noncomputable def pushforward (splitting : SchemeSplitting X p) (morphism : X ⟶ Y)
    [IsIso morphism.c] : SchemeSplitting Y p where
  onOpen U := (splitting.onOpen (morphism ⁻¹ᵁ U)).transport
    (asIso (morphism.app U)).symm.commRingCatIsoToRingEquiv
  restrict_comm {U V} h s := by
    have heval (W : Y.Opens) (a : Γ(Y, W)) :
        morphism.app W
          ((splitting.onOpen (morphism ⁻¹ᵁ W)).transport
            (asIso (morphism.app W)).symm.commRingCatIsoToRingEquiv a) =
        splitting.onOpen (morphism ⁻¹ᵁ W) (morphism.app W a) := by
      exact (asIso (morphism.app W)).commRingCatIsoToRingEquiv.apply_symm_apply _
    have hpreimage : morphism ⁻¹ᵁ V ≤ morphism ⁻¹ᵁ U := fun _ hx ↦ h hx
    have hnaturality (a : Γ(Y, U)) :
        morphism.app V (Y.presheaf.map (homOfLE h).op a) =
          X.presheaf.map (homOfLE hpreimage).op (morphism.app U a) := by
      exact congrArg (fun f : Γ(Y, U) ⟶ Γ(X, morphism ⁻¹ᵁ V) ↦ f a)
        (morphism.naturality (homOfLE h).op)
    apply (asIso (morphism.app V)).commRingCatIsoToRingEquiv.injective
    change morphism.app V _ = morphism.app V _
    rw [heval, hnaturality, splitting.restrict_comm hpreimage]
    rw [hnaturality, heval]

/-- Pulling back a descended splitting agrees with splitting the pulled back section. -/
theorem pushforward_app (splitting : SchemeSplitting X p) (morphism : X ⟶ Y)
    [IsIso morphism.c] (U : Y.Opens) (s : Γ(Y, U)) :
    morphism.app U ((splitting.pushforward morphism).onOpen U s) =
      splitting.onOpen (morphism ⁻¹ᵁ U) (morphism.app U s) :=
  (asIso (morphism.app U)).commRingCatIsoToRingEquiv.apply_symm_apply _

end FrobeniusSplitting.SchemeSplitting
