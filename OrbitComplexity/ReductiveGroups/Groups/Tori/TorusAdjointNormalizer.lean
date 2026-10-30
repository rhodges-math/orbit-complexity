import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusTangentContainment
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRepresentation
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage
import OrbitComplexity.ReductiveGroups.Groups.Representatives.ReductiveRootReflectionPoint
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Torus Adjoint Normalizer

A point preserving the tangent of a fixed split torus
also preserves its defining Hopf ideal. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K B ι : Type*} [Field K] [CharZero K]
  [CommRing B] [HopfAlgebra K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)

/-- Tangent containment for the original torus forces its defining ideal to
be preserved under fixed-point conjugation. -/
theorem TorusIdeal.mem_conjugation_of_adjoint_tangent_mem
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (I : HopfIdeal K B)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ t : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g (t : 𝔤) ∈ diagonalizableTangentImage π) :
    ∀ a ∈ I, affineGroupConjugationBialgHom g a ∈ I := by
  let c := affineGroupConjugationBialgHom g
  have hc : Function.Surjective c := by
    change Function.Surjective (affineGroupConjugationBialgEquiv g)
    exact (affineGroupConjugationBialgEquiv g).surjective
  let Q := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range
  have hHQ : diagonalizableTangentImage π ≤ Q := by
    intro d hd
    apply (tangent_mem_hopfQuotient_iff I d).mpr
    intro a ha
    exact (tangent_mem_range_iff_kills_kernel π hπ d).mp hd a
      ((hker a).mpr ha)
  have hJ : (derivationCompLieHom (B := K) (π.comp c)).range ≤ Q := by
    rw [derivationCompLieHom_comp]
    intro z hz
    obtain ⟨d, rfl⟩ := hz
    have hd : (derivationCompLieHom (B := K) π d) ∈
        diagonalizableTangentImage π := ⟨d, rfl⟩
    have hg := hHQ (hAd ⟨_, hd⟩)
    change derivationComp (B := K) c (derivationComp (B := K) π d) ∈ Q
    rw [show c = affineGroupConjugationBialgHom g from rfl,
      DerivationComp.conjugation]
    simpa only [affineGroupAdjointRepresentation_apply,
      derivationCompLieHom_apply] using hg
  have hkill := TorusCoordinateMap.kills_of_tangent_containment
    (π.comp c) (hπ.comp hc) I hJ
  intro a ha
  exact (hker (c a)).mp (hkill a ha)

/-- If the adjoint action maps the torus tangent onto itself, conjugation by
the original point preserves the original torus ideal in both directions. -/
theorem TorusIdeal.iff_of_adjoint_tangent_bijective
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (I : HopfIdeal K B)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ t : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g (t : 𝔤) ∈ diagonalizableTangentImage π)
    (honto : ∀ t : diagonalizableTangentImage π,
      ∃ u : diagonalizableTangentImage π,
        affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤))
    (a : B) :
    affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I := by
  have hAdInv : ∀ t : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g⁻¹ (t : 𝔤) ∈ diagonalizableTangentImage π := by
    intro t
    obtain ⟨u, hu⟩ := honto t
    have heq : affineGroupAdjointRepresentation g⁻¹ (t : 𝔤) = (u : 𝔤) := by
      rw [← hu, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [heq]
    exact u.property
  have hforward := TorusIdeal.mem_conjugation_of_adjoint_tangent_mem
    π hπ I hker g hAd
  have hbackward := TorusIdeal.mem_conjugation_of_adjoint_tangent_mem
    π hπ I hker g⁻¹ hAdInv
  constructor
  · intro ha
    have hb := hbackward (affineGroupConjugationBialgHom g a) ha
    have heq : affineGroupConjugationBialgHom g⁻¹
        (affineGroupConjugationBialgHom g a) = a := by
      exact (affineGroupConjugationBialgEquiv g).left_inv a
    rwa [heq] at hb
  · exact hforward a

/-- Conjugation by the original point normalizes the fixed torus point
subgroup over every commutative value algebra. -/
theorem TorusPointSubgroup.mem_iff_of_adjoint_tangent_bijective
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (I : HopfIdeal K B)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ t : diagonalizableTangentImage π,
      affineGroupAdjointRepresentation g (t : 𝔤) ∈ diagonalizableTangentImage π)
    (honto : ∀ t : diagonalizableTangentImage π,
      ∃ u : diagonalizableTangentImage π,
        affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤))
    {A : Type*} [CommRing A] [Algebra K A]
    (x : WithConv (B →ₐ[K] A)) :
    let s : WithConv (B →ₐ[K] A) :=
      WithConv.toConv ((IsScalarTower.toAlgHom K K A).comp g.ofConv)
    s * x * s⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K A) ↔
    x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K A) := by
  dsimp only
  let s : WithConv (B →ₐ[K] A) :=
    WithConv.toConv ((IsScalarTower.toAlgHom K K A).comp g.ofConv)
  have hpoint := affineGroupConjugationAlgHom_point g x
  change WithConv.toConv (x.ofConv.comp (affineGroupConjugationAlgHom g)) =
    s * x * s⁻¹ at hpoint
  rw [← hpoint,
    TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  have hstable (a : B) : affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I :=
    TorusIdeal.iff_of_adjoint_tangent_bijective
      π hπ I hker g hAd honto a
  constructor
  · intro hx a ha
    let b := (affineGroupConjugationBialgEquiv g).symm a
    have hb : b ∈ I := by
      apply (hstable b).mp
      change (affineGroupConjugationBialgEquiv g) b ∈ I
      simpa only [b, BialgEquiv.apply_symm_apply] using ha
    have hxb := hx b hb
    change x.ofConv (affineGroupConjugationBialgHom g b) = 0 at hxb
    change x.ofConv ((affineGroupConjugationBialgEquiv g)
      ((affineGroupConjugationBialgEquiv g).symm a)) = 0 at hxb
    simpa only [BialgEquiv.apply_symm_apply] using hxb
  · intro hx a ha
    change x.ofConv (affineGroupConjugationAlgHom g a) = 0
    exact hx _ ((hstable a).mpr ha)

universe u
variable {K' B' ι' : Type u} [Field K'] [IsAlgClosed K'] [CharZero K']
  [CommRing B'] [HopfAlgebra K' B'] [Algebra.FiniteType K' B'] [Finite ι']

/-- The rank-one reflection point normalizes the original fixed
maximal torus ideal. Its tangent reflection formula and ideal equality hold
for the same point. -/
theorem TorusAdjointNormalizer.exists_root_reflection_normalizer
    (I : HopfIdeal K' B')
    (hI : HopfIdeal.IsMaximalTorus K' (CommHopfAlgCat.of K' B') I)
    (π : B' →ₐc[K'] MonoidAlgebra K' (Multiplicative (ι' →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B', π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K'
      (FiniteTypeCommHopfAlgCat.of K' B'))
    (α : Multiplicative (ι' →₀ ℤ))
    (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) (hα : α ≠ 1) :
    ∃ (g : WithConv (B' →ₐ[K'] K')) (h : diagonalizableTangentImage π),
      characterDifferentialOnImage π hπ α h = 2 ∧
      (∀ t : diagonalizableTangentImage π,
        affineGroupAdjointRepresentation g
          (t : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K')) =
          (t : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K')) -
            characterDifferentialOnImage π hπ α t •
              (h : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K'))) ∧
      (∀ a : B', affineGroupConjugationBialgHom g a ∈ I ↔ a ∈ I) := by
  obtain ⟨g, h, hh, hg⟩ :=
    reductive_exists_root_reflection_point I hI π hπ hker hB α hocc hα
  let χ := characterDifferentialOnImage π hπ α
  let H := diagonalizableTangentImage π
  let R : H → H := fun t =>
    ⟨affineGroupAdjointRepresentation g
      (t : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K')), by
      rw [hg t]
      exact H.sub_mem t.property (H.smul_mem _ h.property)⟩
  have hR (t : H) : R t = t - χ t • h := by
    apply Subtype.ext
    exact hg t
  have hR2 (t : H) : R (R t) = t := by
    rw [hR (R t), hR t]
    have hhχ : χ h = 2 := hh
    simp only [map_sub, map_smul, hhχ]
    module
  have hAd : ∀ t : H,
      affineGroupAdjointRepresentation g
        (t : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K')) ∈ H :=
    fun t => (R t).property
  have honto : ∀ t : H, ∃ u : H,
      affineGroupAdjointRepresentation g
        (u : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K')) =
          (t : Derivation K' B' (Bialgebra.CounitAlgebra K' B' K')) := by
    intro t
    exact ⟨R t, congrArg Subtype.val (hR2 t)⟩
  exact ⟨g, h, hh, hg,
    TorusIdeal.iff_of_adjoint_tangent_bijective
      π hπ I hker g hAd honto⟩

end ReductiveGroups
