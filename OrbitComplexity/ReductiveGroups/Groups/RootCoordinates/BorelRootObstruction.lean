import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCharacterRoots
import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableRootSubset

/-!
# Borel Root Obstruction

Opposite torus characters cannot both occur inside one solvable
Lie subalgebra of the reductive tangent. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
private theorem characterDifferentialOnImage_inv'
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (α : Multiplicative (ι →₀ ℤ)) :
    characterDifferentialOnImage π hπ α⁻¹ =
      -characterDifferentialOnImage π hπ α := by
  simp only [characterDifferentialOnImage, characterDifferential_inv]
  rfl

/-- A solvable subalgebra of the reductive tangent cannot contain
both original character spaces for a nonidentity occurring character and
its inverse. The Killing hypothesis is used only after quotienting the
tangent by its center. -/
theorem SolvableTangent.not_contains_opposite_characterWeights
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K 𝔤) [LieAlgebra.IsSolvable S]
    (α : Multiplicative (ι →₀ ℤ))
    (hα : α ≠ 1) (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥)
    (hpos : ∀ x : 𝔤, x ∈ affineGroupCharacterWeightSpace π α → x ∈ S)
    (hneg : ∀ x : 𝔤, x ∈ affineGroupCharacterWeightSpace π α⁻¹ → x ∈ S) :
    False := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let Hq := centerQuotientCartan H
  let q := centerQuotientLieHom (K := K) (L := 𝔤)
  let S' := S.map q
  have hS'eq : S' = (q.comp S.incl).range := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxS, rfl⟩ := (S.mem_map q y).mp hy
      exact ⟨⟨x, hxS⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (S.mem_map q _).mpr ⟨x, x.property, rfl⟩
  let _ : LieAlgebra.IsSolvable S' := by
    rw [hS'eq]
    infer_instance
  let χ := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ⟨α, hocc, hα⟩
  have hχeval (t : H) : (χ.val : Hq → K) (centerQuotientCartanMap H t) =
      characterDifferentialOnImage π hπ α t :=
    ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB
      ⟨α, hocc, hα⟩ t
  have htransfer (β : Hq → K) (hβ : β ≠ 0)
      (γ : Multiplicative (ι →₀ ℤ))
      (heval : ∀ t : H, β (centerQuotientCartanMap H t) =
        characterDifferentialOnImage π hπ γ t)
      (hγ : ∀ x : 𝔤, x ∈ affineGroupCharacterWeightSpace π γ → x ∈ S) :
      ∀ y : 𝔤 ⧸ LieAlgebra.center K 𝔤,
        y ∈ LieAlgebra.rootSpace Hq β → y ∈ S' := by
    intro y hy
    obtain ⟨x, hx⟩ := centerQuotientRootSpaceMap_surjective H β ⟨y, hy⟩
    have heq : (fun t : H => β (centerQuotientCartanMap H t)) =
        characterDifferentialOnImage π hπ γ := by
      funext t
      exact heval t
    have hxW : (x : 𝔤) ∈ affineGroupCharacterWeightSpace π γ := by
      rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ γ]
      change (x : 𝔤) ∈ LieAlgebra.rootSpace H
        (characterDifferentialOnImage π hπ γ)
      exact heq ▸ x.property
    have hmap : q (x : 𝔤) ∈ S' :=
      (S.mem_map q _).mpr ⟨x, hγ x hxW, rfl⟩
    have hxy : q (x : 𝔤) = y := congrArg Subtype.val hx
    exact hxy ▸ hmap
  have hχ0 : χ.val.IsNonZero := LieSubalgebra.isNonZero_coe_root χ
  have hχfn : (χ.val : Hq → K) ≠ 0 := by
    intro hz
    apply hχ0
    exact hz
  have hpos' : ∀ y : 𝔤 ⧸ LieAlgebra.center K 𝔤,
      y ∈ LieAlgebra.rootSpace Hq χ.val → y ∈ S' :=
    htransfer χ.val hχfn
      α hχeval hpos
  have hnegEval (t : H) : (-χ.val : Hq →ₗ[K] K) (centerQuotientCartanMap H t) =
      characterDifferentialOnImage π hπ α⁻¹ t := by
    rw [characterDifferentialOnImage_inv', LinearMap.neg_apply]
    exact congrArg Neg.neg (hχeval t)
  have hneg' : ∀ y : 𝔤 ⧸ LieAlgebra.center K 𝔤,
      y ∈ LieAlgebra.rootSpace Hq (-χ.val) → y ∈ S' :=
    htransfer (-χ.val) (neg_ne_zero.mpr hχfn)
      α⁻¹ hnegEval hneg
  exact SolvableSubalgebra.not_contains_opposite_rootSpaces Hq S' χ.val
    hχ0 hpos' hneg'

end ReductiveGroups
