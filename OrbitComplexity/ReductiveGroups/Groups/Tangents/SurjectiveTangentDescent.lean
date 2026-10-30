import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# Surjective Tangent Descent

A tangent descends to a closed subgroup exactly when it annihilates
that subgroup's coordinate ideal. Both the subgroup coordinate algebra and its
tangent differential come from the same Hopf quotient. -/

noncomputable section
namespace ReductiveGroups

variable {K A B : Type*} [Field K]
  [CommRing A] [HopfAlgebra K A] [CommRing B] [HopfAlgebra K B]

private theorem tangent_eq_of_image_eq
    (ρ : A →ₐc[K] B)
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K))
    (hd : ∀ a, ρ a = 0 → d a = 0) {a b : A} (h : ρ a = ρ b) :
    d a = d b := by
  have hz := hd (a - b) (by simp [h])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- Descent of a counit-valued tangent along a surjective coordinate map. -/
def surjectiveTangentDescend
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K))
    (hd : ∀ a, ρ a = 0 → d a = 0) :
    Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K) := by
  let eA := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K
  let eB := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K
  let D : A →ₗ[K] K := eA.toLinearMap.comp d.toLinearMap
  let s := Function.surjInv hρ
  have hs (b : B) : ρ (s b) = b := Function.rightInverse_surjInv hρ b
  have hD {a b : A} (h : ρ a = ρ b) : D a = D b :=
    congrArg eA (tangent_eq_of_image_eq ρ d hd h)
  have hDl (a b : A) : D (a * b) =
      Coalgebra.counit (R := K) a * D b + Coalgebra.counit (R := K) b * D a := by
    change eA (d (a * b)) = _
    rw [d.leibniz, map_add]
    exact congrArg₂ HAdd.hAdd
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul K A K a (d b))
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul K A K b (d a))
  have hcounit (a : A) : Coalgebra.counit (R := K) a =
      Coalgebra.counit (R := K) (ρ a) :=
    (DFunLike.congr_fun (BialgHom.counitAlgHom_comp ρ) a).symm
  refine
    { toFun := fun b => eB.symm (D (s b))
      map_add' := ?_
      map_smul' := ?_
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · intro b c
    rw [hD (a := s (b + c)) (b := s b + s c) (by simp only [map_add, hs]),
      map_add, map_add]
  · intro r b
    rw [hD (a := s (r • b)) (b := r • s b) (by simp only [map_smul, hs]),
      D.map_smul, map_smul]
    rfl
  · change eB.symm (D (s 1)) = 0
    rw [hD (a := s 1) (b := 1) (by simp only [map_one, hs])]
    change eB.symm (eA (d 1)) = 0
    rw [d.map_one_eq_zero, map_zero, map_zero]
  · intro b c
    change eB.symm (D (s (b * c))) =
      b • eB.symm (D (s c)) + c • eB.symm (D (s b))
    apply eB.injective
    rw [AlgEquiv.apply_symm_apply, map_add,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [hD (a := s (b * c)) (b := s b * s c) (by simp only [map_mul, hs]), hDl]
    simp only [hcounit, hs]
    rfl

/-- Pulling the descended tangent back gives precisely the original tangent. -/
theorem surjectiveTangentDescend_comp
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K))
    (hd : ∀ a, ρ a = 0 → d a = 0) :
    TauCeti.derivationComp (B := K) ρ
      (surjectiveTangentDescend ρ hρ d hd) = d := by
  ext a
  apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K).injective
  rw [TauCeti.algEquivSelf_derivationComp_apply]
  change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K)
    (d (Function.surjInv hρ (ρ a))) = _
  rw [tangent_eq_of_image_eq ρ d hd (Function.rightInverse_surjInv hρ (ρ a))]

/-- Exact description of the tangent image of a closed subgroup. -/
theorem tangent_mem_range_iff_kills_kernel
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K) ρ).range ↔
      ∀ a, ρ a = 0 → d a = 0 := by
  constructor
  · rintro ⟨e, rfl⟩ a ha
    change TauCeti.derivationComp (B := K) ρ e a = 0
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K).injective
    rw [map_zero, TauCeti.algEquivSelf_derivationComp_apply]
    change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K) (e (ρ a)) = 0
    rw [ha, map_zero, map_zero]
  · intro hd
    exact ⟨surjectiveTangentDescend ρ hρ d hd,
      surjectiveTangentDescend_comp ρ hρ d hd⟩

end ReductiveGroups
