import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.RootSubsetCoordinates
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductPartition
import Mathlib.Logic.Equiv.Set

/-!
# Multiplication of closed root-support groups

A concatenated root order identifies multiplication for a disjoint closed support
decomposition with an isomorphism of coordinate algebras. Its value on coordinate
classes is the tensor quotient of the group comultiplication.
-/

set_option maxHeartbeats 400000

noncomputable section
namespace ReductiveGroups.BorelRootSubset
open TauCeti
open scoped TensorProduct
universe u
section Partition
variable {α : Type u} (S S₁ S₂ : Set α) (hunion : S = S₁ ∪ S₂)
  (hdisj : Disjoint S₁ S₂)

private def partitionMap : S₁ ⊕ S₂ → S
  | .inl i => ⟨i.val, hunion.symm ▸ Or.inl i.property⟩
  | .inr i => ⟨i.val, hunion.symm ▸ Or.inr i.property⟩

private def partitionEquiv : S₁ ⊕ S₂ ≃ S := Equiv.ofBijective
  (partitionMap S S₁ S₂ hunion) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact congrArg (fun q : S => q.val) hab
        | inr b =>
          have hv : a.val = b.val := congrArg (fun q : S => q.val) hab
          exact False.elim (Set.disjoint_left.mp hdisj a.property (hv ▸ b.property))
      | inr a =>
        cases b with
        | inl b =>
          have hv : a.val = b.val := congrArg (fun q : S => q.val) hab
          exact False.elim (Set.disjoint_left.mp hdisj (hv ▸ b.property) a.property)
        | inr b =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact congrArg (fun q : S => q.val) hab
    · intro r
      have hr : r.val ∈ S₁ ∨ r.val ∈ S₂ := hunion ▸ r.property
      rcases hr with hr | hr
      · exact ⟨.inl ⟨r.val, hr⟩, Subtype.ext rfl⟩
      · exact ⟨.inr ⟨r.val, hr⟩, Subtype.ext rfl⟩)

private def partitionOrder (l : List S₁) (m : List S₂) : List S :=
  (l.map Sum.inl ++ m.map Sum.inr).map (partitionEquiv S S₁ S₂ hunion hdisj)

private theorem partitionOrder_nodup (l : List S₁) (m : List S₂)
    (hl : l.Nodup) (hm : m.Nodup) :
    (partitionOrder S S₁ S₂ hunion hdisj l m).Nodup := by
  apply List.Nodup.map (partitionEquiv S S₁ S₂ hunion hdisj).injective
  refine List.nodup_append.mpr ⟨hl.map Sum.inl_injective, hm.map Sum.inr_injective, ?_⟩
  intro a ha b hb heq
  obtain ⟨i, _, hi⟩ := List.mem_map.mp ha
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hb
  cases hi.trans (heq.trans hj.symm)

private theorem partitionOrder_complete (l : List S₁) (m : List S₂)
    (hl : ∀ i, i ∈ l) (hm : ∀ i, i ∈ m) :
    ∀ i, i ∈ partitionOrder S S₁ S₂ hunion hdisj l m := by
  intro i
  apply List.mem_map.mpr
  refine ⟨(partitionEquiv S S₁ S₂ hunion hdisj).symm i, ?_,
    (partitionEquiv S S₁ S₂ hunion hdisj).apply_symm_apply i⟩
  cases (partitionEquiv S S₁ S₂ hunion hdisj).symm i with
  | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a, hl a, rfl⟩)
  | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b, hm b, rfl⟩)


end Partition

variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]
variable (I J : HopfIdeal K B) (hJI : J ≤ I)
  (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
  (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
  (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
  (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
  (e : Module.Basis (borelRootCharacterIndex J π) K
    (derivationCompLieHom (B := K) (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
  (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
  (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
  (S S₁ S₂ : Set (borelRootCharacterIndex J π))
  (hS : IsBorelRootCharacterClosed J π S)
  (hS₁ : IsBorelRootCharacterClosed J π S₁) (hS₂ : IsBorelRootCharacterClosed J π S₂)
  (hunion : S = S₁ ∪ S₂) (hdisj : Disjoint S₁ S₂)

/-- Multiplication for disjoint closed root supports is an isomorphism of coordinate algebras. -/
def productCoordinateEquiv (l : List S₁) (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    (m : List S₂) (hm : m.Nodup) (hmall : ∀ i, i ∈ m) :
    (B ⧸ (ideal I J hJI hI hJ π hπ hker hB x e he hx S hS).toIdeal) ≃ₐ[K]
      (B ⧸ (ideal I J hJI hI hJ π hπ hker hB x e he hx S₁ hS₁).toIdeal) ⊗[K]
        (B ⧸ (ideal I J hJI hI hJ π hπ hker hB x e he hx S₂ hS₂).toIdeal) :=
  ((coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S hS
    (partitionOrder S S₁ S₂ hunion hdisj l m)
    (partitionOrder_nodup S S₁ S₂ hunion hdisj l m hl hm)
    (partitionOrder_complete S S₁ S₂ hunion hdisj l m hall hmall)).trans
      (MvPolynomial.renameEquiv K (partitionEquiv S S₁ S₂ hunion hdisj).symm)).trans
    ((Algebra.TensorProduct.congr
      (coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S₁ hS₁ l hl hall)
      (coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S₂ hS₂ m hm hmall)).trans
        (MvPolynomial.tensorEquivSum K S₁ S₂ K)).symm


/-- On coordinate classes the product isomorphism is the restricted group multiplication. -/
theorem productCoordinateEquiv_mk
    (l : List S₁) (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    (m : List S₂) (hm : m.Nodup) (hmall : ∀ i, i ∈ m) (b : B) :
    productCoordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S S₁ S₂ hS hS₁ hS₂
      hunion hdisj l hl hall m hm hmall (Ideal.Quotient.mk _ b) =
      ((Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ K (ideal I J hJI hI hJ π hπ hker hB x e he hx S₁ hS₁).toIdeal)
        (Ideal.Quotient.mkₐ K (ideal I J hJI hI hJ π hπ hker hB x e he hx S₂ hS₂).toIdeal)).comp
          (Bialgebra.comulAlgHom K B)) b := by
  let E := partitionEquiv S S₁ S₂ hunion hdisj
  let C₁ := coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S₁ hS₁ l hl hall
  let C₂ := coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S₂ hS₂ m hm hmall
  let C := (Algebra.TensorProduct.congr C₁ C₂).trans
    (MvPolynomial.tensorEquivSum K S₁ S₂ K)
  let q₁ := Ideal.Quotient.mkₐ K (ideal I J hJI hI hJ π hπ hker hB x e he hx S₁ hS₁).toIdeal
  let q₂ := Ideal.Quotient.mkₐ K (ideal I J hJI hI hJ π hπ hker hB x e he hx S₂ hS₂).toIdeal
  have h₁ : C₁.toAlgHom.comp q₁ = gaProductCoordinate (fun i : S₁ => x i.val) l := by
    rfl
  have h₂ : C₂.toAlgHom.comp q₂ = gaProductCoordinate (fun i : S₂ => x i.val) m := by
    rfl
  have hmap : (Algebra.TensorProduct.congr C₁ C₂).toAlgHom.comp
      (Algebra.TensorProduct.map q₁ q₂) =
      Algebra.TensorProduct.map (gaProductCoordinate (fun i : S₁ => x i.val) l)
        (gaProductCoordinate (fun i : S₂ => x i.val) m) := by
    change (Algebra.TensorProduct.map C₁.toAlgHom C₂.toAlgHom).comp _ = _
    rw [← Algebra.TensorProduct.map_comp, h₁, h₂]
  apply C.injective
  change C (C.symm ((MvPolynomial.renameEquiv K E.symm)
    (coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S hS
      (partitionOrder S S₁ S₂ hunion hdisj l m)
      (partitionOrder_nodup S S₁ S₂ hunion hdisj l m hl hm)
      (partitionOrder_complete S S₁ S₂ hunion hdisj l m hall hmall)
        (Ideal.Quotient.mk _ b)))) = _
  rw [C.apply_symm_apply, coordinateEquiv_mk]
  have hrename := gaProductCoordinate_map (fun i : S => x i.val) E
    (l.map Sum.inl ++ m.map Sum.inr)
  have heval := DFunLike.congr_fun hrename b
  change gaProductCoordinate (fun i : S => x i.val)
    (partitionOrder S S₁ S₂ hunion hdisj l m) b =
      (MvPolynomial.renameEquiv K E)
        (gaProductCoordinate (fun i => x (E i).val) (l.map Sum.inl ++ m.map Sum.inr) b) at heval
  rw [heval]
  change (MvPolynomial.renameEquiv K E).symm
    ((MvPolynomial.renameEquiv K E) _) = _
  rw [AlgEquiv.symm_apply_apply]
  have hsum := DFunLike.congr_fun (gaProductCoordinate_sum (fun i => x (E i).val) l m) b
  change gaProductCoordinate (fun i => x (E i).val) (l.map Sum.inl ++ m.map Sum.inr) b = _
  rw [hsum]
  change _ = (MvPolynomial.tensorEquivSum K S₁ S₂ K)
    (((Algebra.TensorProduct.congr C₁ C₂).toAlgHom.comp
      (Algebra.TensorProduct.map q₁ q₂)) ((Bialgebra.comulAlgHom K B) b))
  rw [hmap]
  rfl

end ReductiveGroups.BorelRootSubset
