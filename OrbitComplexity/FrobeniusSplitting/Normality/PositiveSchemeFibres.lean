import OrbitComplexity.FrobeniusSplitting.Normality.Models.PositiveFibreDescent
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.AffineNormality
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normality from positive-characteristic scheme fibres

Affine scalar comparisons turn normal stalks on positive-characteristic fibres
into normal tensor coordinate rings. The algebraic fibre criterion then gives
normal stalks on the integral generic fibre.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

open private coordinates_finitePresentation from
  OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

private theorem normal_tensor_fibre {S L : Type u} [CommRing S] [Field L]
    [Algebra S L] {D : Scheme.{u}} (d : D ⟶ Spec (.of S))
    (U : D.Opens) (hU : IsAffineOpen U)
    (hI : IrreducibleSpace (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap S L))) d : Scheme.{u}))
    (hn : ∀ y : (pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) d : Scheme.{u}),
      IsDomain ((pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) d :
        Scheme.{u}).presheaf.stalk y) ∧
      IsIntegrallyClosed ((pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) d :
        Scheme.{u}).presheaf.stalk y)) :
    letI : Algebra S Γ(U.toScheme, ⊤) :=
      ((U.ι ≫ d).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    Subsingleton (L ⊗[S] Γ(U.toScheme, ⊤)) ∨
      (IsDomain (L ⊗[S] Γ(U.toScheme, ⊤)) ∧
        IsIntegrallyClosed (L ⊗[S] Γ(U.toScheme, ⊤))) := by
  let : Algebra S Γ(U.toScheme, ⊤) :=
    ((U.ι ≫ d).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : IsAffine U.toScheme := hU
  let β := Spec.map (CommRingCat.ofHom (algebraMap S L))
  let DL := (pullback β d : Scheme.{u})
  let qL : DL ⟶ D := pullback.snd β d
  let tL : DL ⟶ Spec (.of L) := pullback.fst β d
  let V := qL ⁻¹ᵁ U
  let : IsAffineHom qL := MorphismProperty.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback β d) inferInstance
  let : IrreducibleSpace DL := hI
  have hV : IsAffineOpen V := hU.preimage qL
  have hq : IsPullback qL tL d β := (IsPullback.of_hasPullback β d).flip
  have hchart : IsPullback (qL ∣_ U) (V.ι ≫ tL) (U.ι ≫ d) β :=
    (isPullback_morphismRestrict qL U).paste_vert hq
  let : Algebra L Γ(V.toScheme, ⊤) :=
    ((V.ι ≫ tL).appTop.hom.comp (Scheme.ΓSpecIso (.of L)).inv.hom).toAlgebra
  obtain ⟨E, _, _, _⟩ := exists_affine_scalar_coordinates
    (U.ι ≫ d) (V.ι ≫ tL) (qL ∣_ U) hchart
  let T : Γ(DL, V) ≃+* (L ⊗[S] Γ(U.toScheme, ⊤)) :=
    (V.topIso.commRingCatIsoToRingEquiv).symm.trans E.symm.toRingEquiv
  exact normal_coordinates_or_subsingleton hn hV T

/-- An integral generic fibre has integrally closed domain stalks if all
positive-characteristic field fibres are irreducible with integrally closed
domain stalks. -/
theorem normal_stalks_of_positive_fibres {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) (D : Over (Spec (.of S)))
    [LocallyOfFinitePresentation D.hom] (X : Over (Spec (.of K))) [IsIntegral X.left]
    (q : X.left ⟶ D.left)
    (hq : IsPullback q X.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hfibres : ∀ (L : Type u) [Field L] [Algebra S L], (ringChar L).Prime →
      IrreducibleSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap S L)))
        D.hom : Scheme.{u}) ∧
      ∀ y : (pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) D.hom : Scheme.{u}),
        IsDomain ((pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) D.hom :
          Scheme.{u}).presheaf.stalk y) ∧
        IsIntegrallyClosed ((pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) D.hom :
          Scheme.{u}).presheaf.stalk y)) :
    ∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.left.presheaf.stalk x) := by
  let : IsAffineHom q := MorphismProperty.of_isPullback
    (P := @IsAffineHom) hq.flip inferInstance
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show q x ∈ (⊤ : D.left.Opens) by trivial)
  let V := q ⁻¹ᵁ U
  have hxV : x ∈ V := hx
  have hV : IsAffineOpen V := hU.preimage q
  let : IsAffine U.toScheme := hU
  let : Nonempty V.toScheme := ⟨⟨x, hxV⟩⟩
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : Algebra S Γ(U.toScheme, ⊤) :=
    ((U.ι ≫ D.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : IsAffine (Over.mk (U.ι ≫ D.hom)).left := hU
  let : LocallyOfFinitePresentation (Over.mk (U.ι ≫ D.hom)).hom :=
    (inferInstance : LocallyOfFinitePresentation (U.ι ≫ D.hom))
  let : Algebra.FinitePresentation S Γ(U.toScheme, ⊤) :=
    coordinates_finitePresentation (.of S) (Over.mk (U.ι ≫ D.hom))
  let : Algebra K Γ(V.toScheme, ⊤) :=
    ((V.ι ≫ X.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have hchart : IsPullback (q ∣_ U) (V.ι ≫ X.hom) (U.ι ≫ D.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) :=
    (isPullback_morphismRestrict q U).paste_vert hq
  obtain ⟨E, _, _, _⟩ := exists_affine_scalar_coordinates
    (U.ι ≫ D.hom) (V.ι ≫ X.hom) (q ∣_ U) hchart
  have hnormal : IsIntegrallyClosed Γ(V.toScheme, ⊤) :=
    normal_of_positive_model_fibres (K := K) (A := Γ(V.toScheme, ⊤))
      (M := Γ(U.toScheme, ⊤)) S hS E (fun L _ _ hp =>
      normal_tensor_fibre (S := S) (L := L) D.hom U hU (hfibres L hp).1 (hfibres L hp).2)
  let : IsIntegrallyClosed Γ(V.toScheme, ⊤) := hnormal
  let : IsIntegrallyClosed Γ(X.left, V) :=
    IsIntegrallyClosed.of_equiv (V.topIso.commRingCatIsoToRingEquiv)
  exact ⟨isDomain_stalk hV hxV, isIntegrallyClosed_stalk hV hxV⟩

end FrobeniusSplitting
