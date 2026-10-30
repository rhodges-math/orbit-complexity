import OrbitComplexity.FrobeniusSplitting.Normality.DenseOpen
import OrbitComplexity.FrobeniusSplitting.Normality.WeakNormal
import OrbitComplexity.FrobeniusSplitting.Splittings.Restriction
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms to split schemes

A finite universally injective surjective morphism to a Frobenius-split scheme is
an isomorphism if its source is reduced and noetherian and its restriction over a
dense target open is an isomorphism. The affine proof embeds source sections into
the sections of that open and applies the finite conductor argument.

## References

* Brion and Kumar, *Frobenius splitting methods in geometry and representation
  theory*, Proposition 1.2.5.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-- A finite universally injective morphism onto a split affine scheme is an isomorphism
if it is an isomorphism over a dense target open. -/
theorem isIso_of_finite_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [IsFinite f] [UniversallyInjective f] [Surjective f]
    [IsReduced X] [NoetherianSpace X] {q : ℕ} [Fact q.Prime]
    [CharP Γ(Y, ⊤) q] (splitting : SchemeSplitting Y q)
    (U : Y.Opens) (hdense : Dense (U : Set Y)) [IsIso (f ∣_ U)] : IsIso f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsReduced Y := splitting.isReduced (Fact.out : q.Prime).one_lt
  have : IsSchemeTheoreticallyDominant f := .of_isDominant _
  have : IsIso (f.app U) := app_isIso_of_restrict f U
  have hopen : IsOpenMap f :=
    (isHomeomorph_iff_continuous_isClosedMap_bijective.2
      ⟨f.continuous, f.isClosedMap, f.injective, f.surjective⟩).isOpenMap
  have hpreimage : Dense ((f ⁻¹ᵁ U : X.Opens) : Set X) := hdense.preimage hopen
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let K := Γ(Y, U)
  let rX : B ⟶ Γ(X, f ⁻¹ᵁ U) :=
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op
  let rY : A ⟶ K := Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  let j : B ⟶ K := rX ≫ inv (f.app U)
  have hfactor : f.appTop ≫ j = rY := by
    have hnat : rY ≫ f.app U = f.appTop ≫ rX :=
      f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
    calc
      f.appTop ≫ j = (f.appTop ≫ rX) ≫ inv (f.app U) := (Category.assoc ..).symm
      _ = (rY ≫ f.app U) ≫ inv (f.app U) := congrArg (· ≫ inv (f.app U)) hnat.symm
      _ = rY := by simp
  let : Algebra A B := f.appTop.hom.toAlgebra
  let : Algebra B K := j.hom.toAlgebra
  let : Algebra A K := rY.hom.toAlgebra
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' <|
    congrArg CommRingCat.Hom.hom hfactor.symm
  have hj : Function.Injective j :=
    ((ConcreteCategory.isIso_iff_bijective (inv (f.app U))).1 inferInstance).injective.comp
      (restrict_injective (f ⁻¹ᵁ U) hpreimage)
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hj
  have : Module.Finite A B := (RingHom.finite_algebraMap).1 f.finite_appTop
  have := UniversallyInjective.respectsIso
  have : UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    change UniversallyInjective (Spec.map f.appTop)
    exact (MorphismProperty.arrow_mk_iso_iff (@UniversallyInjective : MorphismProperty Scheme)
      (arrowIsoSpecΓOfIsAffine f)).1 inferInstance
  have hsurj : Function.Surjective f.appTop :=
    surjective_of_finite_specMap (splitting.onOpen ⊤) (splitting.onOpen U)
      (fun a ↦ splitting.restrict_comm le_top a)
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2
    ⟨f.app_injective ⊤, hsurj⟩
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (arrowIsoSpecΓOfIsAffine f)).2 inferInstance

/-- A finite universally injective morphism onto a split scheme is an isomorphism
if it is an isomorphism over a dense target open. -/
theorem isIso_of_finite {K : Type u} [Field K] {q : ℕ} [Fact q.Prime] [CharP K q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (base : Y ⟶ Spec (.of K))
    [IsFinite f] [UniversallyInjective f] [Surjective f] [IsReduced X] [NoetherianSpace X]
    (splitting : SchemeSplitting Y q) (h : IsIsoOverDense f) : IsIso f := by
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y)).2
  intro V
  have : IsAffine V.1.toScheme := V.2
  have : UniversallyInjective (f ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict (P := @UniversallyInjective) inferInstance V.1
  have : Surjective (f ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance V.1
  have : IsFinite (f ∣_ V.1) := inferInstance
  have : IsReduced (f ⁻¹ᵁ V.1).toScheme := isReduced_of_isOpenImmersion (f ⁻¹ᵁ V.1).ι
  have : NoetherianSpace (f ⁻¹ᵁ V.1).toScheme :=
    (Opens.isOpenEmbedding (f ⁻¹ᵁ V.1)).isInducing.noetherianSpace
  rcases isEmpty_or_nonempty V.1 with hempty | hnonempty
  · have : IsEmpty V.1.toScheme := hempty
    exact isIso_of_isEmpty (f ∣_ V.1)
  · have : Nonempty (⊤ : V.1.toScheme.Opens) :=
      ⟨⟨Classical.choice hnonempty, trivial⟩⟩
    have : CharP Γ(V.1.toScheme, ⊤) q := charP_sections (V.1.ι ≫ base) ⊤
    obtain ⟨U, hdense, hiso⟩ := h.restrict V.1
    exact isIso_of_finite_affine (f ∣_ V.1) (splitting.restrict V.1) U hdense

end FrobeniusSplitting
