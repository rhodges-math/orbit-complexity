import Mathlib.RingTheory.TensorProduct.Maps
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams

/-! # Coordinate diagrams over isomorphic integer bases -/

noncomputable section

universe u v w

namespace FrobeniusSplitting

section Part1

open scoped TensorProduct

private theorem integer_hom_eq {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* ℤ) (f : S →+* T) (s : S) : f s = (e s : T) := by
  have hs : s = ((e s : ℤ) : S) := by
    apply e.injective
    simp only [map_intCast, Int.cast_id]
  calc
    f s = f ((e s : ℤ) : S) := congrArg f hs
    _ = (e s : T) := map_intCast f _

/-- An integer base represented by an isomorphic ring gives the same scalar tensor product. -/
noncomputable def integerScalarEquiv {S R F : Type*}
    [CommRing S] [CommRing R] [CommRing F] [Algebra S R] [Algebra S F]
    (e : S ≃+* ℤ) : R ⊗[ℤ] F ≃ₐ[R] R ⊗[S] F := by
  letI : Algebra S ℤ := e.toRingHom.toAlgebra
  letI : IsScalarTower ℤ S R := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := S) (A := R) (Subsingleton.elim _ _)
  letI : IsScalarTower ℤ S F := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := S) (A := F) (Subsingleton.elim _ _)
  letI : IsScalarTower S ℤ R := IsScalarTower.of_algebraMap_eq fun s ↦ by
    change algebraMap S R s = (e s : R)
    exact integer_hom_eq e (algebraMap S R) s
  letI : IsScalarTower S ℤ F := IsScalarTower.of_algebraMap_eq fun s ↦ by
    change algebraMap S F s = (e s : F)
    exact integer_hom_eq e (algebraMap S F) s
  exact Algebra.TensorProduct.equivOfCompatibleSMul S ℤ R R F

/-- The isomorphic-integer-base tensor comparison fixes pure tensors. -/
theorem integerScalarEquiv_tmul {S R F : Type*}
    [CommRing S] [CommRing R] [CommRing F] [Algebra S R] [Algebra S F]
    (e : S ≃+* ℤ) (r : R) (f : F) :
    integerScalarEquiv e (r ⊗ₜ[ℤ] f) = r ⊗ₜ[S] f := rfl

end Part1

section Part2

open CategoryTheory
open scoped TensorProduct

/-- Tensoring the underlying integer algebras gives a diagram over the coefficient ring. -/
def integerFibreDiagram {J : Type v} [Category.{w} J]
    (R : Type u) [CommRing R] {S : Type*} [CommRing S]
    (G : J ⥤ CommAlgCat.{u} S) : J ⥤ CommAlgCat.{u} R where
  obj i := CommAlgCat.of R (R ⊗[ℤ] G.obj i)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R)
    (G.map f).hom.toRingHom.toIntAlgHom)
  map_id i := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      change r ⊗ₜ[ℤ] (G.map (𝟙 i)).hom a = r ⊗ₜ[ℤ] a
      rw [G.map_id]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      change r ⊗ₜ[ℤ] (G.map (f ≫ g)).hom a =
        r ⊗ₜ[ℤ] (G.map g).hom ((G.map f).hom a)
      rw [G.map_comp]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensor diagrams over isomorphic integer bases have the same coordinate transitions. -/
noncomputable def integerCoordinateScalarIso {J : Type v} [Category.{w} J]
    (R : Type u) [CommRing R] {S : Type u} [CommRing S] [Algebra S R]
    (e : S ≃+* ℤ) (G : J ⥤ CommAlgCat.{u} S) :
    integerFibreDiagram R G ≅
      fixedFibreDiagram (R := R) (M := R) G :=
  NatIso.ofComponents (fun i ↦ CommAlgCat.isoMk
    (integerScalarEquiv (R := R) (F := G.obj i) e)) (by
      intro i j f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      change integerScalarEquiv e (Algebra.TensorProduct.map (AlgHom.id R R)
          (G.map f).hom.toRingHom.toIntAlgHom z) =
        Algebra.TensorProduct.map (AlgHom.id R R) (G.map f).hom (integerScalarEquiv e z)
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change integerScalarEquiv e (a ⊗ₜ[ℤ] (G.map f).hom b) =
          Algebra.TensorProduct.map (AlgHom.id R R) (G.map f).hom
            (integerScalarEquiv e (a ⊗ₜ[ℤ] b))
        rw [integerScalarEquiv_tmul, integerScalarEquiv_tmul]
        rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

end Part2

end FrobeniusSplitting
