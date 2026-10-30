import OrbitComplexity.ReductiveGroups.Groups.SL2.MatrixIntegration
import OrbitComplexity.ReductiveGroups.Groups.SL2.ClosedSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Lie
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentDeterminesMorphism

/-! # Integration of the chosen simple-root pairs -/

noncomputable section

namespace ReductiveGroups

open TauCeti LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

omit [CharZero K] [IsAlgClosed K] in
private theorem elementary_matrix_tangent {n : ℕ}
    (φ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      TauCeti.SpecialLinear.coordinateHopfAlgebra K 2)
    {i j : Fin 2} (hij : i ≠ j) :
    affineGroupMatrixDifferential n φ
        ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm
          (SpecialLinear.single i j hij (1 : K))) =
      GeneralLinear.tangentMatrix n (gaAffineGroupTangent
        ((TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom.comp φ)) := by
  have ht : (TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm
      (SpecialLinear.single i j hij (1 : K)) =
        derivationComp (B := K)
          (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom
          (gaOriginDerivation K) := by
    apply (TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).injective
    change TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2
      ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm
        (SpecialLinear.single i j hij (1 : K))) =
      TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2 _
    rw [LieEquiv.apply_symm_apply, BinaryForms.root_tangent]
  rw [ht, affineGroupMatrixDifferential_apply, gaAffineGroupTangent]
  have h := LinearMap.congr_fun
    (derivationComp_comp (B := K)
      (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom φ)
    (gaOriginDerivation K)
  rw [LinearMap.comp_apply] at h
  exact congrArg (GeneralLinear.tangentMatrix n) h.symm

omit [CharZero K] [IsAlgClosed K] in
private theorem cancel_bialg_comp {A B C : Type*} [CommRing A] [HopfAlgebra K A]
    [CommRing B] [HopfAlgebra K B] [CommRing C] [HopfAlgebra K C]
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ) {f g : B →ₐc[K] C}
    (h : f.comp ρ = g.comp ρ) : f = g := by
  ext b
  obtain ⟨a, rfl⟩ := hρ b
  exact congrArg (fun q : A →ₐc[K] C => q a) h

namespace ReductiveGroupData

variable (G : ReductiveGroupData K)

/-- The chosen positive and negative simple parameters are the two elementary
subgroups of an algebraic `SL₂` morphism with the specified differential. -/
theorem exists_simpleSl2Map (i : G.rootBase.support) :
    ∃ ψ : G.coordinateAlgebra →ₐc[K] TauCeti.SpecialLinear.coordinateHopfAlgebra K 2,
      (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K)
          (zero_ne_one : (0 : Fin 2) ≠ 1)).hom.comp ψ = G.simpleRootMap i ∧
      (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K)
          (one_ne_zero : (1 : Fin 2) ≠ 0)).hom.comp ψ = G.negativeSimpleRootMap i ∧
      ∀ x : SpecialLinear.sl (Fin 2) K,
        derivationComp (B := K) ψ
          ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) =
            G.simpleSl2LieHom i x := by
  obtain ⟨n, ρ, hρ, hinj⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := G.coordinateAlgebra)
  let r := (affineGroupMatrixDifferential n ρ).comp (G.simpleSl2LieHom i)
  obtain ⟨φ, hφ⟩ := exists_sl2_matrixMap K r
  have hGa {a b : Fin 2} (hab : a ≠ b)
      (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
      (hx : G.simpleSl2LieHom i (SpecialLinear.single a b hab (1 : K)) =
        gaAffineGroupTangent x) :
      (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hab).hom.comp φ =
        x.comp ρ := by
    apply gaMorphism_ext_of_tangent_eq
    apply (GeneralLinear.tangentLieEquivMatrix (R := K) (B := K) n).injective
    change GeneralLinear.tangentMatrix n (gaAffineGroupTangent _) =
      GeneralLinear.tangentMatrix n (gaAffineGroupTangent _)
    calc
      _ = affineGroupMatrixDifferential n φ
          ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm
            (SpecialLinear.single a b hab (1 : K))) :=
        (elementary_matrix_tangent φ hab).symm
      _ = r (SpecialLinear.single a b hab (1 : K)) := hφ _
      _ = affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x) :=
        congrArg (affineGroupMatrixDifferential n ρ) hx
      _ = _ := by
        change GeneralLinear.tangentMatrix n
          (derivationComp (B := K) ρ (derivationComp (B := K) x (gaOriginDerivation K))) =
            GeneralLinear.tangentMatrix n
              (derivationComp (B := K) (x.comp ρ) (gaOriginDerivation K))
        have h := LinearMap.congr_fun (derivationComp_comp (B := K) x ρ)
          (gaOriginDerivation K)
        rw [LinearMap.comp_apply] at h
        exact congrArg (GeneralLinear.tangentMatrix n) h.symm
  have hp := hGa (zero_ne_one : (0 : Fin 2) ≠ 1) (G.simpleRootMap i)
    (by rw [← slFinTwoBasis_zero, G.simpleSl2LieHom_basis]; rfl)
  have hn := hGa (one_ne_zero : (1 : Fin 2) ≠ 0) (G.negativeSimpleRootMap i)
    (by rw [← slFinTwoBasis_one, G.simpleSl2LieHom_basis]; rfl)
  have hroot : ∀ (a b : Fin 2) (hab : a ≠ b),
      ∃ x : G.coordinateAlgebra →ₐc[K] TauCeti.AdditiveGroup.coordinateHopfAlgebra K,
        x.comp ρ =
          (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hab).hom.comp φ := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim (hab rfl)
    · exact ⟨G.simpleRootMap i, hp.symm⟩
    · exact ⟨G.negativeSimpleRootMap i, hn.symm⟩
    · exact False.elim (hab rfl)
  obtain ⟨ψ, hψ, _⟩ := existsUnique_sl2_factor ρ hρ φ hroot
  refine ⟨ψ, ?_, ?_, fun x => ?_⟩
  · apply cancel_bialg_comp ρ hρ
    rw [BialgHom.comp_assoc, hψ]
    exact hp
  · apply cancel_bialg_comp ρ hρ
    rw [BialgHom.comp_assoc, hψ]
    exact hn
  · apply hinj
    calc
      _ = affineGroupMatrixDifferential n φ
          ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) := by
        simp only [affineGroupMatrixDifferential_apply]
        have h := LinearMap.congr_fun (derivationComp_comp (B := K) ψ ρ)
          ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x)
        rw [LinearMap.comp_apply, hψ] at h
        exact congrArg (GeneralLinear.tangentMatrix n) h.symm
      _ = _ := hφ x

end ReductiveGroupData

end ReductiveGroups
