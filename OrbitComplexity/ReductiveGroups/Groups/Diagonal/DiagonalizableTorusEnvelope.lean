import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTorusFactor
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusQuotientTangent
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike

/-!
# Diagonalizable Torus Envelope

A torus envelope of an original diagonalizable finite-type affine group,
retaining the original coordinate Hopf algebra and fixed torus subgroup. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

private theorem torusEnvelope_of_presentation
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K)
    (I : TauCeti.HopfIdeal K H)
    (hI : TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I))
    (M : Type u) [CommGroup M] [Group.FG M]
    (e : MonoidAlgebra K M ≃ₐc[K] H) :
    ∃ J : TauCeti.HopfIdeal K H,
      J ≤ I ∧
      TauCeti.torusCommHopfAlgProperty K
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) ∧
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient H.obj J).hom).range = ⊤ := by
  let φ : H →ₐc[K] MonoidAlgebra K (M ⧸ CommGroup.torsion M) :=
    torsionFreeCoordinateMap.comp e.symm.toBialgHom
  have hφ : Function.Surjective φ :=
    torsionFreeCoordinateMap_surjective.comp e.symm.surjective
  let J : TauCeti.HopfIdeal K H := TauCeti.HopfIdeal.kerOfSurjective φ hφ
  refine ⟨J, ?_, ?_, ?_⟩
  · obtain ⟨n, π, hπ, hker⟩ := exists_torusCoordinateMap H I hI
    intro a ha
    have ha' : e.symm a ∈
        (torsionFreeTorusIdeal (K := K) (M := M)).toIdeal := by
      apply (TauCeti.HopfIdeal.mem_kerOfSurjective _ _).mpr
      have hz := (TauCeti.HopfIdeal.mem_kerOfSurjective φ hφ).mp ha
      change torsionFreeCoordinateMap (e.symm a) = 0 at hz
      exact hz
    have hz := RingHom.mem_ker.mp
      (torsionFreeTorusIdeal_le_ker (π.comp e.toBialgHom) ha')
    have hza : π a = 0 := by
      change π (e (e.symm a)) = 0 at hz
      simpa only [BialgEquiv.apply_symm_apply] using hz
    exact (TauCeti.HopfIdeal.mem_toIdeal).mp ((hker a).mp hza)
  · let f : CommHopfAlgCat.of K H ⟶
        CommHopfAlgCat.of K (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) :=
      CommHopfAlgCat.ofHom φ
    let ei : TauCeti.FiniteTypeCommHopfAlgCat.quotient H J ≅
        TauCeti.FiniteTypeCommHopfAlgCat.of K
          (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) :=
      ObjectProperty.isoMk _
        (TauCeti.CommHopfAlgCat.quotientKerOfSurjectiveIso f hφ)
    exact (TauCeti.torusCommHopfAlgProperty K).prop_of_iso ei.symm
      (torsionFreeCoordinate_torus (K := K) (M := M))
  · let q := (TauCeti.CommHopfAlgCat.mkQuotient H.obj J).hom
    let eb := TauCeti.HopfIdeal.kerLiftBialgEquiv φ hφ
    have he : Function.Surjective
        (TauCeti.derivationCompLieHom (B := K) e.symm.toBialgHom) := by
      intro d
      refine ⟨TauCeti.derivationCompLieHom (B := K) e.toBialgHom d, ?_⟩
      rw [← LieHom.comp_apply, ← TauCeti.derivationCompLieHom_comp]
      have hid : e.toBialgHom.comp e.symm.toBialgHom = BialgHom.id K H :=
        BialgEquiv.comp_symm e
      rw [hid, TauCeti.derivationCompLieHom_id]
      rfl
    have hq : Function.Surjective
        (TauCeti.derivationCompLieHom (B := K)
          (torsionFreeCoordinateMap (K := K) (M := M))) := by
      intro d
      obtain ⟨x, hx⟩ := TorsionFreeCoordinateMap.tangent_surjective
        (K := K) (M := M) d
      exact ⟨x, by simpa only [TauCeti.derivationCompLieHom_apply] using hx⟩
    have hφtan : Function.Surjective
        (TauCeti.derivationCompLieHom (B := K) φ) := by
      change Function.Surjective (TauCeti.derivationCompLieHom (B := K)
        (torsionFreeCoordinateMap.comp e.symm.toBialgHom))
      rw [TauCeti.derivationCompLieHom_comp]
      exact he.comp hq
    have hcomp : eb.toBialgHom.comp q = φ := by
      exact TauCeti.HopfIdeal.kerLiftBialgHom_comp_mkBialgHom φ hφ
    calc
      (TauCeti.derivationCompLieHom (B := K) q).range =
          (TauCeti.derivationCompLieHom (B := K)
            (eb.toBialgHom.comp q)).range :=
        (tangentImage_comp_bialgEquiv q eb).symm
      _ = (TauCeti.derivationCompLieHom (B := K) φ).range := by rw [hcomp]
      _ = ⊤ := (LieHom.range_eq_top _).mpr hφtan

/-- An original finite-type diagonalizable group has a torus closed subgroup
containing any fixed torus subgroup and carrying its entire tangent Lie
algebra. The ambient Hopf algebra and fixed torus ideal remain unchanged. -/
theorem diagonalizable_exists_torusEnvelope
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K)
    (hH : TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K H)
    (I : TauCeti.HopfIdeal K H)
    (hI : TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)) :
    ∃ J : TauCeti.HopfIdeal K H,
      J ≤ I ∧
      TauCeti.torusCommHopfAlgProperty K
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) ∧
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient H.obj J).hom).range = ⊤ := by
  have : Group.FG (GroupLike K H) :=
    TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top K H
      (inferInstanceAs (Algebra.FiniteType K H)) hH
  have hspan : Submodule.span K
      (Set.range (GroupLike.val (R := K) (A := H))) = ⊤ :=
    (TauCeti.Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top
      (R := K) (C := H)).1 hH
  let e : MonoidAlgebra K (GroupLike K H) ≃ₐc[K] H :=
    TauCeti.GroupLike.evaluationBialgEquiv K H hspan
  exact torusEnvelope_of_presentation H I hI (GroupLike K H) e

end ReductiveGroups
