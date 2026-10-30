import OrbitComplexity.SchubertGeometry.Normality.SchubertBorelCharacter
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositiveCharacter
import OrbitComplexity.ReductiveGroups.Groups.Reductive.TorusConjugation
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCoroots
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialInjective

/-! # The full torus lattice under a fixed simple representative -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti WithConv
universe u v
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def coordinates : G.torusAlgebra ≃ₐc[K] MonoidAlgebra K G.characters :=
  BialgEquiv.ofBijective (torusCharacterCoordinates G) ⟨by
    have hk (a : G.torusAlgebra) : torusCharacterCoordinates G a = 0 ↔ a = 0 := by
      refine Quotient.inductionOn' a (fun a => ?_)
      change G.torusSplit a = 0 ↔ Ideal.Quotient.mk G.torusIdeal.toIdeal a = 0
      rw [G.split_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    intro a b hab
    apply sub_eq_zero.mp
    apply (hk (a - b)).mp
    exact (map_sub (torusCharacterCoordinates G) a b).trans
      (by rw [hab, sub_self]), by
    intro y
    obtain ⟨a, ha⟩ := G.split_surjective y
    exact ⟨Ideal.Quotient.mk G.torusIdeal.toIdeal a, ha⟩⟩

private def conjugationMap (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    MonoidAlgebra K G.characters →ₐc[K] MonoidAlgebra K G.characters :=
  (coordinates G).toBialgHom.comp
    ((G.torusConjugation g hg).toBialgHom.comp (coordinates G).symm.toBialgHom)

/-- The simple-reflection torus map in the split coordinates.
This wrapper preserves the private map used by the existing reflection formulas. -/
def reflectionTorusMap (i : G.rootBase.support) :
    MonoidAlgebra K G.characters →ₐc[K] MonoidAlgebra K G.characters :=
  conjugationMap G (G.reflectionPoint i.val)
    (G.isBruhatSystem.rankOne i).mem_normalizer

omit [CharZero K] in
private theorem conjugation_square (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    (conjugationMap G g hg).comp G.torusSplit =
      G.torusSplit.comp (affineGroupConjugationBialgHom g) := by
  apply BialgHom.ext
  intro a
  have ha : (coordinates G).symm (G.torusSplit a) =
      Ideal.Quotient.mk G.torusIdeal.toIdeal a := by
    let qa : G.torusAlgebra := Ideal.Quotient.mk G.torusIdeal.toIdeal a
    have he : coordinates G qa = G.torusSplit a := rfl
    exact (congrArg (fun y => (coordinates G).symm y) he).symm.trans
      ((coordinates G).symm_apply_apply qa)
  change coordinates G (G.torusConjugation g hg
    ((coordinates G).symm (G.torusSplit a))) = _
  rw [ha, G.torusConjugation_mk]
  rfl

omit [CharZero K] in
private theorem conjugation_tangent (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points))
    (h : Derivation K (MonoidAlgebra K G.characters)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K G.characters) K)) :
    derivationComp (B := K) G.torusSplit
        (derivationComp (B := K) (conjugationMap G g hg) h) =
      affineGroupAdjointRepresentation g (derivationComp (B := K) G.torusSplit h) := by
  have hc := congrArg (fun f => derivationComp (B := K) f h)
    (conjugation_square G g hg)
  simp only [derivationComp_comp, LinearMap.comp_apply] at hc
  exact hc.trans (by
    rw [DerivationComp.conjugation, affineGroupAdjointRepresentation_apply])

omit [CharZero K] in
private theorem conjugation_character_diff (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points))
    (chi : G.characters)
    (h : Derivation K (MonoidAlgebra K G.characters)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K G.characters) K)) :
    characterDifferential (K := K)
        (MonoidAlgebra.mapDomainOfBialgHom (conjugationMap G g hg) chi) h =
      characterDifferential chi
        (derivationComp (B := K) (conjugationMap G g hg) h) := by
  simp only [characterDifferential_apply, MonoidAlgebra.single_mapDomainOfBialgHom]
  rw [algEquivSelf_derivationComp_apply]
  rfl

private def differentialHom : G.characters →* Multiplicative
    (Derivation K (MonoidAlgebra K G.characters)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K G.characters) K) →ₗ[K] K) where
  toFun chi := Multiplicative.ofAdd (characterDifferential chi)
  map_one' := by simp
  map_mul' a b := by simp [characterDifferential_mul]

omit [IsAlgClosed K] [CharZero K] in
private theorem differential_zpow (chi : G.characters) (z : ℤ) :
    characterDifferential (K := K) (chi ^ z) = z • characterDifferential chi :=
  congrArg Multiplicative.toAdd (map_zpow (differentialHom G) chi z)

/-- The fixed representative acts on every character of the full torus lattice. -/
theorem simpleReflection_character (i : G.rootBase.support) (chi : G.characters) :
    MonoidAlgebra.mapDomainOfBialgHom
        (conjugationMap G (G.reflectionPoint i.val)
          (G.isBruhatSystem.rankOne i).mem_normalizer) chi =
      chi * G.rootCharacter i.val ^ (-Coroot.simpleCorootFunctional G i chi.toAdd) := by
  let n := G.reflectionPoint i.val
  let hn := (G.isBruhatSystem.rankOne i).mem_normalizer
  let E := diagonalizableTangentEquivImage G.torusSplit G.split_surjective
  apply characterDifferential_injective (K := K)
  apply LinearMap.ext
  intro h
  let t := E h
  have hR := (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive
      (G.characterRootEquiv.symm i.val)).adjoint_rootReflectionPoint G.split_surjective t
  change affineGroupAdjointRepresentation n (t : G.tangent) =
    (t : G.tangent) - characterDifferentialOnImage G.torusSplit G.split_surjective
      (G.rootCharacter i.val) t • (Coroot.simpleCartan G i : G.tangent) at hR
  have ht : E (derivationComp (B := K) (conjugationMap G n hn) h) =
      t - characterDifferential (G.rootCharacter i.val) h • Coroot.simpleCartan G i := by
    apply Subtype.ext
    change derivationComp (B := K) G.torusSplit
        (derivationComp (B := K) (conjugationMap G n hn) h) =
      (t : G.tangent) - characterDifferential (G.rootCharacter i.val) h •
        (Coroot.simpleCartan G i : G.tangent)
    have hr : characterDifferentialOnImage G.torusSplit G.split_surjective
        (G.rootCharacter i.val) t = characterDifferential (G.rootCharacter i.val) h :=
      characterDifferentialOnImage_apply_equiv _ _ _ _
    exact (conjugation_tangent G n hn h).trans (hR.trans
      (congrArg (fun k : K => (t : G.tangent) - k •
        (Coroot.simpleCartan G i : G.tangent)) hr))
  rw [conjugation_character_diff]
  calc
    _ = characterDifferentialOnImage G.torusSplit G.split_surjective chi
        (E (derivationComp (B := K) (conjugationMap G n hn) h)) :=
      (characterDifferentialOnImage_apply_equiv _ _ _ _).symm
    _ = characterDifferential chi h -
        characterDifferential (G.rootCharacter i.val) h *
          (Coroot.simpleCorootFunctional G i chi.toAdd : K) := by
      rw [ht, map_sub, map_smul, characterDifferentialOnImage_apply_equiv]
      have hc : characterDifferentialOnImage G.torusSplit G.split_surjective chi
          (Coroot.simpleCartan G i) = (Coroot.simpleCorootFunctional G i chi.toAdd : K) :=
        (Coroot.simpleCorootFunctional_cast G i chi.toAdd).symm
      exact congrArg (fun k : K => characterDifferential chi h -
        characterDifferential (G.rootCharacter i.val) h * k) hc
    _ = _ := by
      rw [characterDifferential_mul, differential_zpow]
      change characterDifferential chi h - characterDifferential (G.rootCharacter i.val) h *
          (Coroot.simpleCorootFunctional G i chi.toAdd : K) =
        characterDifferential chi h + (-Coroot.simpleCorootFunctional G i chi.toAdd) •
          characterDifferential (G.rootCharacter i.val) h
      rw [zsmul_eq_mul, Int.cast_neg]
      ring

/-- The regular torus map is the original group conjugation over every coefficient algebra. -/
theorem simpleReflection_torus_points {A : Type v} [CommRing A] [Algebra K A]
    (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] A)) :
    AlgHom.mapDomain G.torusSplit
        (AlgHom.mapDomain (conjugationMap G (G.reflectionPoint i.val)
          (G.isBruhatSystem.rankOne i).mem_normalizer) z) =
      toConv ((IsScalarTower.toAlgHom K K A).comp (G.reflectionPoint i.val).ofConv) *
        AlgHom.mapDomain G.torusSplit z *
          (toConv ((IsScalarTower.toAlgHom K K A).comp
            (G.reflectionPoint i.val).ofConv))⁻¹ := by
  change ((AlgHom.mapDomain G.torusSplit).comp
    (AlgHom.mapDomain (conjugationMap G (G.reflectionPoint i.val)
      (G.isBruhatSystem.rankOne i).mem_normalizer))) z = _
  rw [← AlgHom.mapDomain_comp, conjugation_square, AlgHom.mapDomain_comp]
  exact affineGroupConjugationAlgHom_point _ _

/-- The same full character identity holds on units over arbitrary coefficient algebras. -/
theorem simpleReflection_character_eval {A : Type v} [CommRing A] [Algebra K A]
    (i : G.rootBase.support) (chi : G.characters)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] A)) :
    DiagonalizableGroup.pointsMulEquiv
        (AlgHom.mapDomain (conjugationMap G (G.reflectionPoint i.val)
          (G.isBruhatSystem.rankOne i).mem_normalizer) z) chi =
      DiagonalizableGroup.pointsMulEquiv z chi *
        DiagonalizableGroup.pointsMulEquiv z (G.rootCharacter i.val) ^
          (-Coroot.simpleCorootFunctional G i chi.toAdd) := by
  let c := conjugationMap G (G.reflectionPoint i.val)
    (G.isBruhatSystem.rankOne i).mem_normalizer
  change DiagonalizableGroup.pointsMulEquiv (AlgHom.mapDomain c z) chi = _
  rw [← MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom c]
  change DiagonalizableGroup.pointsMulEquiv
    (DiagonalizableGroup.pointsMap (MonoidAlgebra.mapDomainOfBialgHom c) z) chi = _
  rw [DiagonalizableGroup.pointsMulEquiv_pointsMap]
  change DiagonalizableGroup.pointsMulEquiv z
    (MonoidAlgebra.mapDomainOfBialgHom c chi) = _
  rw [simpleReflection_character, map_mul, map_zpow]

/-- The fixed odd positive-root character has its prescribed full-torus transformation. -/
theorem simpleReflection_odd_eval {A : Type v} [CommRing A] [Algebra K A]
    (p : ℕ) (hp : Odd p) (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] A)) :
    DiagonalizableGroup.pointsMulEquiv
        (AlgHom.mapDomain (conjugationMap G (G.reflectionPoint i.val)
          (G.isBruhatSystem.rankOne i).mem_normalizer) z) (G.oddRootCharacter p) =
      DiagonalizableGroup.pointsMulEquiv z (G.oddRootCharacter p) *
        DiagonalizableGroup.pointsMulEquiv z (G.rootCharacter i.val) ^ (-((p - 1 : ℕ) : ℤ)) := by
  rw [simpleReflection_character_eval, G.oddRootCharacter_weight p hp]

end SchubertGeometry.ProjectiveLine
