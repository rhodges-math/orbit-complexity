import OrbitComplexity.GroupActions.Varieties.AffineMulTranslations
import OrbitComplexity.GroupActions.Varieties.AffineMulTangents
import OrbitComplexity.GroupActions.Varieties.RationalDifferentials
import Mathlib.RingTheory.RingHom.Smooth

/-! # Smoothness of restricted affine multiplication

Surjectivity of the differential of restricted multiplication propagates from the identity
by coordinate translations. The rational-point differential criterion then gives smoothness.
The differential is surjective whenever the two tangent images span the ambient tangent space.

## Main results

* `GroupActions.affineMulMap_smooth`: a surjective identity differential gives smoothness.
* `GroupActions.affineMulTangent_surjective_of_sup`: spanning tangent images give surjectivity.
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w x

section Tangents

variable {R H A B : Type u} [CommRing R]
  [CommRing H] [Bialgebra R H] [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]

/-- Tangent images spanning the ambient tangent make the multiplication differential surjective. -/
theorem affineMulTangent_surjective_of_sup (f : H →ₐc[R] A) (g : H →ₐc[R] B)
    (h : (TauCeti.derivationCompLieHom (B := R) f).range.toSubmodule ⊔
      (TauCeti.derivationCompLieHom (B := R) g).range.toSubmodule = ⊤) :
    Function.Surjective (affineMulTangent f g) := by
  intro d
  have hd : d ∈ (TauCeti.derivationCompLieHom (B := R) f).range.toSubmodule ⊔
      (TauCeti.derivationCompLieHom (B := R) g).range.toSubmodule := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hd
  obtain ⟨da, hda⟩ := ha
  obtain ⟨db, hdb⟩ := hb
  refine ⟨(Derivation.tensorProductLieEquiv (R := R) (B := R)
    (H₁ := A) (H₂ := B)).symm (da, db), ?_⟩
  rw [affineMulTangent_prod]
  exact (congrArg₂ (· + ·) hda hdb).trans hab

end Tangents

section PointSquares

variable {R : Type u} {S : Type v} {T : Type w} {C : Type x}
  [CommRing R] [CommRing S] [CommRing T] [CommRing C]
  [Algebra R S] [Algebra R T] [Algebra R C]

private theorem pointComp_eq (f : S →ₐ[R] T) (eS : S ≃ₐ[R] S) (eT : T ≃ₐ[R] T)
    (h : eT.toAlgHom.comp f = f.comp eS.toAlgHom) (p : T →ₐ[R] C) :
    (p.comp eT.toAlgHom).comp f = (p.comp f).comp eS.toAlgHom := by
  ext s
  exact congrArg p (AlgHom.congr_fun h s)

private theorem pointDerivationEquiv_natural (f : S →ₐ[R] T)
    (eS : S ≃ₐ[R] S) (eT : T ≃ₐ[R] T)
    (h : eT.toAlgHom.comp f = f.comp eS.toAlgHom) (p : T →ₐ[R] C)
    (d : Derivation R T (PointAlgebra p)) :
    pointDerivationEquiv eS (p.comp f) (pointDerivationPrecomp f p d) =
      pointDerivationCongr (pointComp_eq f eS eT h p)
        (pointDerivationPrecomp f (p.comp eT.toAlgHom) (pointDerivationEquiv eT p d)) := by
  ext s
  apply (PointAlgebra.algEquivSelf ((p.comp f).comp eS.toAlgHom)).injective
  have hL : PointAlgebra.algEquivSelf ((p.comp f).comp eS.toAlgHom)
      (pointDerivationEquiv eS (p.comp f) (pointDerivationPrecomp f p d) s) =
      PointAlgebra.algEquivSelf p (d (f (eS s))) := by
    rfl
  have hR : PointAlgebra.algEquivSelf ((p.comp f).comp eS.toAlgHom)
      (pointDerivationCongr (pointComp_eq f eS eT h p)
        (pointDerivationPrecomp f (p.comp eT.toAlgHom) (pointDerivationEquiv eT p d)) s) =
      PointAlgebra.algEquivSelf p (d (eT (f s))) := by
    erw [pointDerivationCongr_apply]
    rfl
  rw [hL, hR]
  exact congrArg (fun z => PointAlgebra.algEquivSelf p (d z)) (AlgHom.congr_fun h s).symm

/-- Coordinate equivalences commuting with a morphism preserve surjectivity of point derivatives. -/
private theorem surjective_pointPrecomp_equiv (f : S →ₐ[R] T)
    (eS : S ≃ₐ[R] S) (eT : T ≃ₐ[R] T)
    (h : eT.toAlgHom.comp f = f.comp eS.toAlgHom) (p : T →ₐ[R] C) :
    Function.Surjective (pointDerivationPrecomp f p) ↔
      Function.Surjective (pointDerivationPrecomp f (p.comp eT.toAlgHom)) := by
  let eIn := pointDerivationEquiv eT p
  let eOld := pointDerivationEquiv eS (p.comp f)
  let eOut := pointDerivationCongr (pointComp_eq f eS eT h p)
  let old := pointDerivationPrecomp f p
  let new := pointDerivationPrecomp f (p.comp eT.toAlgHom)
  have hfun : eOld ∘ old = eOut ∘ new ∘ eIn :=
    funext (pointDerivationEquiv_natural f eS eT h p)
  calc
    Function.Surjective old ↔ Function.Surjective (eOld ∘ old) :=
      (EquivLike.comp_surjective old eOld).symm
    _ ↔ Function.Surjective (eOut ∘ new ∘ eIn) := by rw [hfun]
    _ ↔ Function.Surjective (new ∘ eIn) := EquivLike.comp_surjective _ eOut
    _ ↔ Function.Surjective new := EquivLike.surjective_comp eIn new


end PointSquares

private theorem tensorPoints_comp_map {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (p : (A →ₐ[K] K) × (B →ₐ[K] K))
    (f : A →ₐ[K] A) (g : B →ₐ[K] B) :
    ((tensorAlgebraPointsEquiv K A B).symm p).comp (Algebra.TensorProduct.map f g) =
      (tensorAlgebraPointsEquiv K A B).symm (p.1.comp f, p.2.comp g) := by
  ext <;> simp [tensorAlgebraPointsEquiv]

private theorem counit_tensor_points {K A B : Type u}
    [CommRing K] [CommRing A] [Bialgebra K A] [CommRing B] [Bialgebra K B] :
    Bialgebra.counitAlgHom K (A ⊗[K] B) =
      (tensorAlgebraPointsEquiv K A B).symm
        (Bialgebra.counitAlgHom K A, Bialgebra.counitAlgHom K B) := by
  ext <;> simp [tensorAlgebraPointsEquiv, Bialgebra.counitAlgHom]


section Algebras

variable {K H A B : Type u} [Field K]
  [CommRing H] [HopfAlgebra K H]
  [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]

private theorem affineMulTangent_surjective_point (f : H →ₐc[K] A) (g : H →ₐc[K] B) :
    Function.Surjective (affineMulTangent f g) ↔
      Function.Surjective (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
        (Bialgebra.counitAlgHom K (A ⊗[K] B))) := by
  let eIn := (counitPointDerivEquiv K (A ⊗[K] B)).symm
  let eOut := (pointDerivationCongr (counit_comp_affineMulMap f g)).trans
    (counitPointDerivEquiv K H)
  let F := pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
    (Bialgebra.counitAlgHom K (A ⊗[K] B))
  change Function.Surjective (eOut ∘ F ∘ eIn) ↔ Function.Surjective F
  exact (EquivLike.surjective_comp eIn (eOut ∘ F)).trans (EquivLike.comp_surjective F eOut)


variable [IsAlgClosed K]
  [Algebra.FiniteType K H] [IsReduced H]
  [Algebra.FiniteType K A] [IsReduced A]
  [Algebra.FiniteType K B] [IsReduced (A ⊗[K] B)]


/-- Surjectivity of a restricted multiplication derivative propagates from the identity. -/
private theorem affineMulMap_deriv_surjective (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (h : Function.Surjective (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
      (Bialgebra.counitAlgHom K (A ⊗[K] B)))) (q : A ⊗[K] B →ₐ[K] K) :
    Function.Surjective (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom) q) := by
  let p := tensorAlgebraPointsEquiv K A B q
  let a := WithConv.toConv p.1
  let b := WithConv.toConv p.2
  let eT := Algebra.TensorProduct.congr (leftTranslationAlgEquiv a)
    (TauCeti.HopfAlgebra.rightTranslationAlgEquiv b)
  let eS := (leftTranslationAlgEquiv (WithConv.toConv (a.ofConv.comp f.toAlgHom))).trans
    (TauCeti.HopfAlgebra.rightTranslationAlgEquiv (WithConv.toConv (b.ofConv.comp g.toAlgHom)))
  have hcomm : eT.toAlgHom.comp (affineMulMap f.toAlgHom g.toAlgHom) =
      (affineMulMap f.toAlgHom g.toAlgHom).comp eS.toAlgHom :=
    affineMulMap_translation f g a b
  have hpoint : (Bialgebra.counitAlgHom K (A ⊗[K] B)).comp eT.toAlgHom = q := by
    rw [counit_tensor_points]
    change ((tensorAlgebraPointsEquiv K A B).symm
      (Bialgebra.counitAlgHom K A, Bialgebra.counitAlgHom K B)).comp
        (Algebra.TensorProduct.map (leftTranslationAlgEquiv a).toAlgHom
          (TauCeti.HopfAlgebra.rightTranslationAlgEquiv b).toAlgHom) = q
    rw [tensorPoints_comp_map, leftTranslationAlgEquiv_toAlgHom,
      TauCeti.HopfAlgebra.rightTranslationAlgEquiv_toAlgHom,
      counit_comp_leftTranslation, TauCeti.HopfAlgebra.counitAlgHom_comp_rightTranslationAlgHom]
    exact (tensorAlgebraPointsEquiv K A B).symm_apply_apply q
  have htranslated := (surjective_pointPrecomp_equiv (affineMulMap f.toAlgHom g.toAlgHom)
    eS eT hcomm (Bialgebra.counitAlgHom K (A ⊗[K] B))).mp h
  erw [hpoint] at htranslated
  exact htranslated

variable [Algebra.Smooth K H] [Algebra.Smooth K (A ⊗[K] B)]

/-- Restricted multiplication is smooth when its identity differential is surjective. -/
theorem affineMulMap_smooth (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (h : Function.Surjective (affineMulTangent f g)) :
    (affineMulMap f.toAlgHom g.toAlgHom).toRingHom.Smooth := by
  let μ := affineMulMap f.toAlgHom g.toAlgHom
  let : Algebra H (A ⊗[K] B) := μ.toRingHom.toAlgebra
  let : IsScalarTower K H (A ⊗[K] B) := IsScalarTower.of_algHom μ
  let : Algebra.FiniteType K (A ⊗[K] B) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K A)
      (inferInstance : Algebra.FiniteType A (A ⊗[K] B))
  let : Algebra.FiniteType H (A ⊗[K] B) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K H (A ⊗[K] B)
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  let : Algebra.FinitePresentation H (A ⊗[K] B) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  change Algebra.Smooth H (A ⊗[K] B)
  apply smooth_of_surjective_rationalDerivs K H (A ⊗[K] B)
  intro q
  have hμ : IsScalarTower.toAlgHom K H (A ⊗[K] B) = μ := by ext; rfl
  rw [hμ]
  exact affineMulMap_deriv_surjective f g ((affineMulTangent_surjective_point f g).mp h) q


end Algebras

end

end GroupActions
