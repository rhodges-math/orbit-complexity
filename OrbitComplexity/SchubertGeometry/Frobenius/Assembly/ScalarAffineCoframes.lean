import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareStacking
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Scalar affine charts for retained coframes

Tensor coordinates identify the scalar affine chart with the chart in the
chosen cover. Both projections are compared before any line module is
transported.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open scoped TensorProduct

open private scalarMap scalarMap_factor from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def chartIso {B : Type u} [CommRing B] {X : Scheme.{u}} [IsAffine X]
    (e : B ≃+* Γ(X, ⊤)) : Spec (.of B) ≅ X :=
  (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm ≪≫ X.isoSpec.symm

private theorem equiv_inverse {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) :
    e.toCommRingCatIso.inv = CommRingCat.ofHom e.symm.toRingHom := by
  ext x
  rfl

private theorem chartIso_hom {B : Type u} [CommRing B]
    {X : Scheme.{u}} [IsAffine X] (e : B ≃+* Γ(X, ⊤)) :
    (chartIso e).hom = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.isoSpec.inv := by
  simp only [chartIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv]
  rw [equiv_inverse]
  rfl

private theorem chartIso_old {B : Type u} [CommRing B]
    {X XT : Scheme.{u}} [IsAffine X] [IsAffine XT]
    (e : B ≃+* Γ(XT, ⊤)) (ι : Γ(X, ⊤) →+* B) (q : XT ⟶ X)
    (he : ∀ x, e (ι x) = q.appTop.hom x) :
    (chartIso e).hom ≫ q = Spec.map (CommRingCat.ofHom ι) ≫ X.isoSpec.inv := by
  have hm : q.appTop ≫ CommRingCat.ofHom e.symm.toRingHom = CommRingCat.ofHom ι := by
    ext x
    change e.symm (q.appTop.hom x) = ι x
    rw [← he x, e.symm_apply_apply]
  rw [chartIso_hom]
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality q, ← Category.assoc,
    ← Spec.map_comp, hm]

private theorem chartIso_field {B : Type u} [CommRing B]
    {P XT : Scheme.{u}} [IsAffine P] [IsAffine XT]
    (e : B ≃+* Γ(XT, ⊤)) (w : B →+* Γ(P, ⊤)) (q : P ⟶ XT)
    (he : w.comp e.symm.toRingHom = q.appTop.hom) :
    Spec.map (CommRingCat.ofHom w) ≫ (chartIso e).hom = P.isoSpec.inv ≫ q := by
  rw [chartIso_hom]
  rw [← Category.assoc, ← Spec.map_comp]
  have hm : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom w = q.appTop := by
    exact CommRingCat.hom_ext he
  rw [hm]
  exact Scheme.isoSpec_inv_naturality q

private theorem coefficient_eq {T K : Type u} [CommRing T] [CommRing K]
    [Algebra T K] {XT P : Scheme.{u}}
    (t : XT ⟶ Spec (.of T)) (b : P ⟶ Spec (.of K)) (q : P ⟶ XT)
    (h : q ≫ t = b ≫ Spec.map (CommRingCat.ofHom (algebraMap T K))) (x : T) :
    let : Algebra T Γ(XT, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of T)).inv.hom).toAlgebra
    let : Algebra K Γ(P, ⊤) :=
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    q.appTop.hom (algebraMap T Γ(XT, ⊤) x) =
      algebraMap K Γ(P, ⊤) (algebraMap T K x) := by
  let : Algebra T Γ(XT, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of T)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    (b.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  change (q ≫ t).appTop.hom ((Scheme.ΓSpecIso (.of T)).inv.hom x) = _
  rw [h]
  have he := congrArg (fun f : CommRingCat.of T ⟶ Γ(P, ⊤) => f.hom x)
    (congrArg (fun f => f ≫ b.appTop)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap T K))))
  exact he.symm

/-- Tensor coordinates identify the scalar affine chart and retain its
old-chart and field-chart projection maps. -/
theorem exists_scalar_affine_chart {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {X XT P : Scheme.{u}} [IsAffine X] [IsAffine P]
    (base : X ⟶ Spec (.of S)) (baseT : XT ⟶ Spec (.of T))
    (baseK : P ⟶ Spec (.of K)) (q : XT ⟶ X)
    (hT : IsPullback q baseT base
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (m : P ⟶ X) (n : P ⟶ XT) (hnq : n ≫ q = m)
    (hnb : n ≫ baseT = baseK ≫ Spec.map (CommRingCat.ofHom (algebraMap T K))) :
    let : Algebra S Γ(X, ⊤) :=
      (base.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : Algebra K Γ(P, ⊤) :=
      (baseK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (e : K ⊗[S] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤))
      (_he : ∀ x, e ((1 : K) ⊗ₜ[S] x) = m.appTop.hom x),
    ∃ I : Spec (.of (T ⊗[S] Γ(X, ⊤))) ≅ XT,
      I.hom ≫ q =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
          X.isoSpec.inv ∧
      Spec.map (CommRingCat.ofHom (scalarMap (R := T) e)) ≫ I.hom =
        P.isoSpec.inv ≫ n := by
  dsimp only
  let : Algebra S Γ(X, ⊤) :=
    (base.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra T Γ(XT, ⊤) :=
    (baseT.appTop.hom.comp (Scheme.ΓSpecIso (.of T)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    (baseK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro e he
  let : IsAffineHom q := MorphismProperty.of_isPullback hT.flip inferInstance
  let : IsAffine XT := isAffine_of_isAffineHom (f := q)
  obtain ⟨eT, _, heT, _⟩ := exists_affine_scalar_coordinates base baseT q hT
  have hcoeff (x : T) : n.appTop.hom (algebraMap T Γ(XT, ⊤) x) =
      algebraMap K Γ(P, ⊤) (algebraMap T K x) :=
    coefficient_eq baseT baseK n hnb x
  have hm : n.appTop.hom.comp eT.toRingHom = scalarMap (R := T) e := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext t
      change n.appTop.hom (eT (algebraMap T (T ⊗[S] Γ(X, ⊤)) t)) =
        e ((algebraMap T K t) ⊗ₜ[S] (1 : Γ(X, ⊤)))
      rw [eT.commutes, hcoeff]
      exact (e.commutes (algebraMap T K t)).symm
    · rw [scalarMap_factor e m.appTop.hom he]
      ext x
      change n.appTop.hom (eT ((1 : T) ⊗ₜ[S] x)) = m.appTop.hom x
      rw [heT]
      change (n ≫ q).appTop.hom x = m.appTop.hom x
      rw [hnq]
  have hcomp : (scalarMap (R := T) e).comp eT.symm.toRingHom = n.appTop.hom := by
    ext x
    change scalarMap (R := T) e (eT.symm x) = n.appTop.hom x
    rw [← hm]
    exact congrArg n.appTop.hom (eT.apply_symm_apply x)
  exact ⟨chartIso eT.toRingEquiv,
    chartIso_old eT.toRingEquiv Algebra.TensorProduct.includeRight.toRingHom q heT,
    chartIso_field eT.toRingEquiv (scalarMap (R := T) e) n hcomp⟩

end SchubertGeometry.RetainedCharacter
