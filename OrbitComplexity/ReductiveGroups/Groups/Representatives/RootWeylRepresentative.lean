import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusAdjointNormalizer
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientSl2Coroot

/-!
# Root Weyl Representative

The original-group point representing a root coreflection on the
Killing quotient of the fixed maximal-torus tangent. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- Integrate a root-positioned `sl₂` triple to its three-factor
point and calculate its action on every vector of the original Cartan. -/
private theorem rootSl2GaPoint_reflection
    [FiniteDimensional K 𝔤] [LieAlgebra.HasCentralRadical K 𝔤]
    (H : LieSubalgebra K 𝔤) [H.IsCartanSubalgebra]
    (χ : Weight K H 𝔤) (hχ : χ.IsNonZero)
    {h e f : 𝔤} (hs : IsSl2Triple h e f)
    (he : e ∈ rootSpace H χ)
    (hf : f ∈ rootSpace H (-(χ : H → K))) :
    ∃ g : WithConv (B →ₐ[K] K), ∀ t : H,
      affineGroupAdjointRepresentation g (t : 𝔤) =
        (t : 𝔤) - χ t • h := by
  have hχ0 : (χ : H → K) ≠ 0 := hχ
  have hχneg : (-(χ : H → K)) ≠ 0 := neg_ne_zero.mpr hχ0
  let x := rootVectorGaMorphism H (χ : H → K) hχ0 e he
  let y := rootVectorGaMorphism H (-(χ : H → K)) hχneg f hf
  let g := gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
    gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
    gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))
  refine ⟨g, ?_⟩
  intro t
  have hte : ⁅(t : 𝔤), e⁆ = χ t • e :=
    CentralRadical.lie_eq_smul_of_mem_rootSpace H χ hχ he t
  have htf : ⁅(t : 𝔤), f⁆ = (-χ t) • f := by
    let χneg : Weight K H 𝔤 := ⟨-(χ : H → K), by
      intro hz
      have hzero : f = 0 :=
        (LieSubmodule.eq_bot_iff (N := rootSpace H (-(χ : H → K)))).mp hz f hf
      exact hs.f_ne_zero hzero⟩
    have hχneg' : χneg.IsNonZero := by
      change (-(χ : H → K)) ≠ 0
      exact hχneg
    have htf' := CentralRadical.lie_eq_smul_of_mem_rootSpace H χneg hχneg' hf t
    change ⁅(t : 𝔤), f⁆ = (-χ t) • f at htf'
    exact htf'
  have hpoint := gaSl2PointProduct_adjoint_reflection x y h (t : 𝔤)
    (χ t) (by simpa [x, y] using hs) (by simpa [x] using hte)
    (by simpa [y] using htf)
  simpa only [g] using hpoint

/-- An occurring original torus character has a normalizing point
whose action on the center quotient is reflection through the
canonical coroot of the descended root. -/
theorem ReductiveRootWeylRepresentative.exists_root_weyl_representative
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
    let χs := nonidentityCharacterLieWeightEquiv π hπ α
    let ψs := nonzeroCenterQuotientWeightEquiv H χs
    ∃ (g : WithConv (B →ₐ[K] K)) (h : H),
      centerQuotientLieHom (K := K) (h : 𝔤) =
        (coroot ψs.val : 𝔤 ⧸ LieAlgebra.center K 𝔤) ∧
      (∀ t : H, affineGroupAdjointRepresentation g (t : 𝔤) =
        (t : 𝔤) - characterDifferentialOnImage π hπ α.val t • (h : 𝔤)) ∧
      (∀ a : B, affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I) ∧
      (∀ t : H,
        centerQuotientLieHom (K := K)
          (affineGroupAdjointRepresentation g (t : 𝔤)) =
          centerQuotientLieHom (K := K) (t : 𝔤) -
            ψs.val (centerQuotientCartanMap H t) •
              (coroot ψs.val : 𝔤 ⧸ LieAlgebra.center K 𝔤)) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let χs := nonidentityCharacterLieWeightEquiv π hπ α
  let ψs := nonzeroCenterQuotientWeightEquiv H χs
  let χ := characterDifferentialOnImage π hπ α.val
  have hχeval (t : H) : χs.val t = χ t :=
    nonidentityCharacterLieWeightEquiv_apply π hπ α t
  obtain ⟨h, e, f, hs, he, hf, hh⟩ :=
    centralRadical_exists_isSl2Triple H χs.val χs.property
  obtain ⟨g, hact⟩ := rootSl2GaPoint_reflection H χs.val χs.property hs he hf
  have hactC (t : H) : affineGroupAdjointRepresentation g (t : 𝔤) =
      (t : 𝔤) - χ t • h := by
    simpa only [hχeval] using hact t
  have hχh : χ (⟨h, hh⟩ : H) = 2 := by
    rw [← hχeval]
    exact centralRadical_sl2_root_apply_eq_two H χs.val χs.property hs he hh
  let q := centerQuotientLieHom (K := K) (L := 𝔤)
  have hqh : q h = (coroot ψs.val : 𝔤 ⧸ LieAlgebra.center K 𝔤) := by
    have hc := centerQuotient_sl2_h_eq_coroot H χs.val χs.property hs he hf hh
    change q h = (coroot ψs.val : 𝔤 ⧸ LieAlgebra.center K 𝔤)
    exact hc
  let R : H → H := fun t =>
    ⟨affineGroupAdjointRepresentation g (t : 𝔤), by
      rw [hactC t]
      exact H.sub_mem t.property (H.smul_mem _ hh)⟩
  have hR (t : H) : R t = t - χ t • (⟨h, hh⟩ : H) := by
    apply Subtype.ext
    exact hactC t
  have hR2 (t : H) : R (R t) = t := by
    rw [hR (R t), hR t]
    simp only [map_sub, map_smul, hχh]
    module
  have hAd : ∀ t : H,
      affineGroupAdjointRepresentation g (t : 𝔤) ∈ H :=
    fun t => (R t).property
  have honto : ∀ t : H, ∃ u : H,
      affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤) := by
    intro t
    exact ⟨R t, congrArg Subtype.val (hR2 t)⟩
  have hideal := TorusIdeal.iff_of_adjoint_tangent_bijective
    π hπ I hker g hAd honto
  refine ⟨g, ⟨h, hh⟩, hqh, hactC, hideal, ?_⟩
  intro t
  rw [hactC t, map_sub, map_smul, hqh]
  have hcoeff : χ t = ψs.val (centerQuotientCartanMap H t) := calc
    χ t = χs.val t := (hχeval t).symm
    _ = ψs.val (centerQuotientCartanMap H t) := by
      exact (NonzeroCenterQuotientWeightEquiv.apply_map H χs t).symm
  rw [hcoeff]

set_option maxHeartbeats 400000 in
/-- The same normalizing point acts on the center-quotient Cartan by
Mathlib's standard root-system coreflection. -/
theorem reductive_exists_root_coreflection_point
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
    let χs := nonidentityCharacterLieWeightEquiv π hπ α
    let ψs := nonzeroCenterQuotientWeightEquiv H χs
    ∃ g : WithConv (B →ₐ[K] K),
      (∀ a : B, affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I) ∧
      ∀ t : H, ∃ s : H,
        (s : 𝔤) = affineGroupAdjointRepresentation g (t : 𝔤) ∧
        centerQuotientCartanMap H s =
          (rootSystem (centerQuotientCartan H)).coreflection
            (⟨ψs.val, by simpa [LieSubalgebra.root] using ψs.property⟩ :
              (centerQuotientCartan H).root)
            (centerQuotientCartanMap H t) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let χs := nonidentityCharacterLieWeightEquiv π hπ α
  let ψs := nonzeroCenterQuotientWeightEquiv H χs
  obtain ⟨g, h, hqh, hact, hideal, hquot⟩ :=
    ReductiveRootWeylRepresentative.exists_root_weyl_representative I hI π hπ hker hB α
  refine ⟨g, hideal, ?_⟩
  intro t
  let s : H := ⟨affineGroupAdjointRepresentation g (t : 𝔤), by
    rw [hact t]
    exact H.sub_mem t.property (H.smul_mem _ h.property)⟩
  refine ⟨s, rfl, ?_⟩
  apply Subtype.ext
  have hq := hquot t
  change centerQuotientLieHom (K := K) (s : 𝔤) = _ at hq ⊢
  rw [hq]
  simp only [RootPairing.coreflection_apply,
    LieAlgebra.IsKilling.rootSystem_coroot_apply]
  rfl

end ReductiveGroups
