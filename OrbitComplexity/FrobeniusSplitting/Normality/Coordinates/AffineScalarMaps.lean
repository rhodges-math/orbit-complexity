import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Batteries.Tactic.Lint

/-! # Global section maps under scalar extension

Tensor coordinates compare global section maps over arbitrary schemes before
any arithmetic model is substituted.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section
universe u

namespace FrobeniusSplitting

/-- The map on global sections of a morphism over an affine base, as an
algebra homomorphism for the structure maps of the two schemes. -/
def affineSectionMap {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (s : X ⟶ Spec (.of S)) (t : Y ⟶ Spec (.of S))
    (f : X ⟶ Y) (h : f ≫ t = s) :
    letI : Algebra S Γ(X, ⊤) :=
      (s.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : Algebra S Γ(Y, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    Γ(Y, ⊤) →ₐ[S] Γ(X, ⊤) := by
  letI : Algebra S Γ(X, ⊤) :=
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  letI : Algebra S Γ(Y, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  refine { f.appTop.hom with commutes' := fun a ↦ ?_ }
  change (f ≫ t).appTop.hom ((Scheme.ΓSpecIso (.of S)).inv.hom a) =
    s.appTop.hom ((Scheme.ΓSpecIso (.of S)).inv.hom a)
  exact congrArg (fun k : X ⟶ Spec (.of S) ↦
    k.appTop.hom ((Scheme.ΓSpecIso (.of S)).inv.hom a)) h

private theorem section_coefficient {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
    (f : X ⟶ Y) (h : f ≫ t = s) (a : R) :
    letI : Algebra R Γ(X, ⊤) :=
      (s.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra R Γ(Y, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    f.appTop.hom (algebraMap R Γ(Y, ⊤) a) = algebraMap R Γ(X, ⊤) a := by
  let : Algebra R Γ(X, ⊤) :=
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra R Γ(Y, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  exact (affineSectionMap s t f h).commutes a

private theorem conjugate_surjective {A B C D : Type*}
    (eA : A ≃ C) (eB : B ≃ D) (f : A → B) (g : C → D)
    (h : ∀ a, g (eA a) = eB (f a)) :
    Function.Surjective f ↔ Function.Surjective g := by
  constructor
  · intro hf d
    obtain ⟨a, ha⟩ := hf (eB.symm d)
    refine ⟨eA a, ?_⟩
    rw [h, ha, eB.apply_symm_apply]
  · intro hg b
    obtain ⟨c, hc⟩ := hg (eB b)
    refine ⟨eA.symm c, eB.injective ?_⟩
    rw [← h, eA.apply_symm_apply, hc]

/-- Surjectivity of a scalar-extended section map is equivalent to
surjectivity of its tensor algebra map, using both Cartesian projections. -/
theorem affine_scalar_map_surjective
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    {X Y XR YR : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (s : X ⟶ Spec (.of S)) (t : Y ⟶ Spec (.of S))
    (f : X ⟶ Y) (h : f ≫ t = s)
    (sR : XR ⟶ Spec (.of R)) (tR : YR ⟶ Spec (.of R))
    (qX : XR ⟶ X) (qY : YR ⟶ Y)
    (hX : IsPullback qX sR s (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hY : IsPullback qY tR t (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (fR : XR ⟶ YR) (hbase : fR ≫ tR = sR) (hmap : fR ≫ qY = qX ≫ f) :
    let : Algebra S Γ(X, ⊤) :=
      (s.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : Algebra S Γ(Y, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    Function.Surjective
      (Algebra.TensorProduct.lTensor (S := R) R (affineSectionMap s t f h)) ↔
      Function.Surjective fR.appTop.hom := by
  let : Algebra S Γ(X, ⊤) :=
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra S Γ(Y, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra R Γ(XR, ⊤) :=
    (sR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra R Γ(YR, ⊤) :=
    (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  obtain ⟨eX, _, _, heX⟩ := exists_affine_scalar_coordinates s sR qX hX
  obtain ⟨eY, _, _, heY⟩ := exists_affine_scalar_coordinates t tR qY hY
  apply conjugate_surjective eY.toEquiv eX.toEquiv
  intro a
  change fR.appTop.hom (eY a) =
    eX ((Algebra.TensorProduct.lTensor (S := R) R (affineSectionMap s t f h)) a)
  induction a using TensorProduct.inductionOn with
  | tmul r y =>
      rw [heY, map_mul, section_coefficient sR tR fR hbase]
      change _ = eX (r ⊗ₜ[S] f.appTop.hom y)
      rw [heX]
      congr 1
      exact congrArg (fun k : XR ⟶ Y ↦ k.appTop.hom y) hmap
  | add a b ha hb => simp only [map_add, ha, hb]

end FrobeniusSplitting
