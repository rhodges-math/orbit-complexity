import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootWeylRepresentative
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCharacterRoots
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalRootEigenvectors
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRadicalCharacteristic

/-!
# Root Reflection Conjugation

Transport of root vectors and their integrated additive subgroups
by an original-group point acting on the fixed torus tangent. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- An adjoint point transports an exact Lie eigenvector according to
its action on the original Cartan. -/
theorem AffineGroupAdjoint.mem_rootSpace_of_eigen_transport
    (H : LieSubalgebra K 𝔤) [LieRing.IsNilpotent H]
    (g : WithConv (B →ₐ[K] K)) (χ χ' : H → K)
    (hAd : ∀ t : H, affineGroupAdjointRepresentation g (t : 𝔤) ∈ H)
    (honto : ∀ t : H, ∃ u : H,
      affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤))
    (hχ : ∀ t : H,
      χ' (⟨affineGroupAdjointRepresentation g (t : 𝔤), hAd t⟩ : H) = χ t)
    (d : 𝔤) (hd : ∀ t : H, ⁅(t : 𝔤), d⁆ = χ t • d) :
    affineGroupAdjointRepresentation g d ∈ rootSpace H χ' := by
  apply weightSpace_le_genWeightSpace
  rw [mem_weightSpace]
  intro t
  obtain ⟨s, hs⟩ := honto t
  have heq := (affineGroupAdjointLieEquiv g).map_lie (s : 𝔤) d
  change ⁅(t : 𝔤), affineGroupAdjointRepresentation g d⁆ =
    χ' t • affineGroupAdjointRepresentation g d
  change affineGroupAdjointRepresentation g ⁅(s : 𝔤), d⁆ =
    ⁅affineGroupAdjointRepresentation g (s : 𝔤),
      affineGroupAdjointRepresentation g d⁆ at heq
  rw [← hs, ← heq, hd, map_smul]
  congr 1
  calc
    χ s = χ' (⟨affineGroupAdjointRepresentation g (s : 𝔤), hAd s⟩ : H) := (hχ s).symm
    _ = χ' t := congrArg χ' (Subtype.ext hs)

variable [IsAlgClosed K] [CharZero K]

/-- The reflection of a quotient root evaluates after the matching Cartan
coreflection as the original root. -/
private theorem quotient_root_reflection_coreflection
    {L : Type u} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieAlgebra.IsKilling K L]
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (α β : H.root) (t : H) :
    ((rootSystem H).reflectionPerm α β).val
      ((rootSystem H).coreflection α t) = β.val t := by
  let P := rootSystem H
  change (P.root (P.reflectionPerm α β)) (P.coreflection α t) = P.root β t
  rw [P.root_reflectionPerm]
  have h := congrArg
    (fun F : H →ₗ[K] Module.Dual K (Module.Dual K H) =>
      F (P.coreflection α t) (P.root β))
    (P.reflection_dualMap_eq_coreflection α)
  simpa [P, LinearEquiv.dualMap_apply, LinearMap.dualMap_apply,
    P.coreflection_same] using h

variable [Algebra.FiniteType K B] {ι : Type u} [Finite ι]

set_option maxHeartbeats 400000 in
/-- The representative of an original root reflection carries every
other original character root space to the character selected by the exact
root-system reflection in the center quotient. -/
theorem RootReflectionConjugation.root_reflection_character_transport
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ∃ g : WithConv (B →ₐ[K] K),
      (∀ a : B, affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I) ∧
      ∀ β : {β : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
        ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π β.val →
          affineGroupAdjointRepresentation g d ∈
            affineGroupCharacterWeightSpace π
              (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
                (E α) (E β))).val := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  let P := rootSystem (centerQuotientCartan H)
  obtain ⟨g, h, hqh, hact, hideal, hquot⟩ :=
    ReductiveRootWeylRepresentative.exists_root_weyl_representative I hI π hπ hker hB α
  refine ⟨g, hideal, ?_⟩
  intro β d hd
  let γ := E.symm (P.reflectionPerm (E α) (E β))
  have hAd (t : H) : affineGroupAdjointRepresentation g (t : 𝔤) ∈ H := by
    rw [hact t]
    exact H.sub_mem t.property (H.smul_mem _ h.property)
  let R : H → H := fun t =>
    ⟨affineGroupAdjointRepresentation g (t : 𝔤), hAd t⟩
  have hR (t : H) : R t = t -
      characterDifferentialOnImage π hπ α.val t • h := by
    apply Subtype.ext
    exact hact t
  have hαh : characterDifferentialOnImage π hπ α.val h = 2 := by
    rw [← ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB α h]
    change (E α).val (centerQuotientCartanMap H h) = 2
    have hcor : centerQuotientCartanMap H h = coroot (E α).val := by
      apply Subtype.ext
      exact hqh
    rw [hcor]
    exact LieAlgebra.IsKilling.root_apply_coroot (LieSubalgebra.isNonZero_coe_root (E α))
  have hR2 (t : H) : R (R t) = t := by
    rw [hR (R t), hR t]
    simp only [map_sub, map_smul, hαh]
    module
  have honto (t : H) : ∃ u : H,
      affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤) :=
    ⟨R t, congrArg Subtype.val (hR2 t)⟩
  have hquotR (t : H) : centerQuotientCartanMap H (R t) =
      P.coreflection (E α) (centerQuotientCartanMap H t) := by
    apply Subtype.ext
    exact hquot t
  have hcoeff (t : H) : characterDifferentialOnImage π hπ γ.val (R t) =
      characterDifferentialOnImage π hπ β.val t := by
    rw [← ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB γ (R t),
      ← ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB β t]
    change (E γ).val (centerQuotientCartanMap H (R t)) =
      (E β).val (centerQuotientCartanMap H t)
    rw [show E γ = P.reflectionPerm (E α) (E β) from E.apply_symm_apply _, hquotR]
    exact quotient_root_reflection_coreflection (centerQuotientCartan H)
      (E α) (E β) (centerQuotientCartanMap H t)
  have hχ : ∀ t : H,
      characterDifferentialOnImage π hπ γ.val (R t) =
        characterDifferentialOnImage π hπ β.val t := hcoeff
  have heigen (t : H) : ⁅(t : 𝔤), d⁆ =
      characterDifferentialOnImage π hπ β.val t • d := by
    let χβ := nonidentityCharacterLieWeightEquiv π hπ β
    have hχβ : (χβ.val : H → K) = characterDifferentialOnImage π hπ β.val := by
      funext u
      exact nonidentityCharacterLieWeightEquiv_apply π hπ β u
    have hdroot : d ∈ rootSpace H (χβ.val : H → K) := by
      rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ β.val] at hd
      change d ∈ rootSpace H (characterDifferentialOnImage π hπ β.val) at hd
      rwa [hχβ]
    rw [← hχβ]
    exact CentralRadical.lie_eq_smul_of_mem_rootSpace H χβ χβ.property hdroot t
  have hroot := AffineGroupAdjoint.mem_rootSpace_of_eigen_transport H g
    (characterDifferentialOnImage π hπ β.val)
    (characterDifferentialOnImage π hπ γ.val) hAd honto hχ d heigen
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ γ.val]
  exact hroot

set_option maxHeartbeats 400000 in
/-- The same point maps each entire original root space *onto* its
reflected-character root space. Equality follows from the one-dimensional
root multiplicities and invertibility of the adjoint action. -/
theorem RootReflectionConjugation.root_reflection_character_space_onto
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ∃ g : WithConv (B →ₐ[K] K),
      (∀ a : B, affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I) ∧
      (∀ β : {β : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
        ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π β.val →
          affineGroupAdjointRepresentation g d ∈
            affineGroupCharacterWeightSpace π
              (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
                (E α) (E β))).val) ∧
      ∀ β : {β : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
        (affineGroupCharacterWeightSpace π β.val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
            affineGroupCharacterWeightSpace π
              (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
                (E α) (E β))).val := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  obtain ⟨g, hideal, hmem⟩ :=
    RootReflectionConjugation.root_reflection_character_transport I hI π hπ hker hB α
  refine ⟨g, hideal, hmem, ?_⟩
  intro β
  let γ := E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm (E α) (E β))
  apply Submodule.eq_of_le_of_finrank_eq
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact hmem β x hx
  · rw [((affineGroupAdjointLieEquiv g).toLinearEquiv).finrank_map_eq]
    exact (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB
      β.val β.property.2 β.property.1).trans
      (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB
        γ.val γ.property.2 γ.property.1).symm

set_option maxHeartbeats 400000 in
/-- The same original-group reflection point conjugates each uniquely
integrated additive root subgroup to the subgroup indexed by the reflected
original character. Its parameter is the image tangent vector, with no
chosen normalization of root vectors. -/
theorem RootReflectionConjugation.exists_root_reflection_ga_conjugation
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ∃ g : WithConv (B →ₐ[K] K),
      (∀ a : B, affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I) ∧
      (∀ β : {β : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
        (affineGroupCharacterWeightSpace π β.val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
            affineGroupCharacterWeightSpace π
              (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
                (E α) (E β))).val) ∧
      ∀ β : {β : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
        ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π β.val →
          ∃ x y : B →ₐc[K] SymmetricAlgebra K K,
            gaAffineGroupTangent x = d ∧
            gaAffineGroupTangent y = affineGroupAdjointRepresentation g d ∧
            affineGroupAdjointRepresentation g d ∈
              affineGroupCharacterWeightSpace π
                (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
                  (E α) (E β))).val ∧
            ∀ t : K,
              g * gaAffineGroupPoints x (Multiplicative.ofAdd t) * g⁻¹ =
                gaAffineGroupPoints y (Multiplicative.ofAdd t) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  obtain ⟨g, hideal, htransport, honto⟩ :=
    RootReflectionConjugation.root_reflection_character_space_onto I hI π hπ hker hB α
  refine ⟨g, hideal, honto, ?_⟩
  intro β d hd
  let γ := E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm (E α) (E β))
  have hd' : affineGroupAdjointRepresentation g d ∈
      affineGroupCharacterWeightSpace π γ.val := htransport β d hd
  obtain ⟨x, hx, _⟩ :=
    CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ β.val β.property.2 d hd
  obtain ⟨y, hy, _⟩ :=
    CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ γ.val γ.property.2
      (affineGroupAdjointRepresentation g d) hd'
  refine ⟨x, y, hx, hy, hd', ?_⟩
  intro t
  have htan : affineGroupAdjointRepresentation g (gaAffineGroupTangent x) =
      (1 : K) • gaAffineGroupTangent y := by
    rw [hx, hy, one_smul]
  simpa only [one_mul] using
    GaAffineGroupPoints.conjugate_of_tangent_eq x y g 1 htan t


end ReductiveGroups
