import OrbitComplexity.SchubertGeometry.Normality.SchubertBorelCharacter
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The affine line with the inverse of a Borel character -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti WithConv
open scoped TensorProduct
universe u v
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- A Borel character evaluated as a unit over the specified coefficient algebra. -/
def borelCharacterUnit {A : Type v} [CommRing A] [Algebra K A] (chi : G.characters) :
    WithConv (G.borelAlgebra →ₐ[K] A) →* Aˣ where
  toFun b := DiagonalizableGroup.pointsMulEquiv
    (AlgHom.mapDomain (borelCharacterMap G chi) b) (Multiplicative.ofAdd 1)
  map_one' := by rw [map_one, map_one]; rfl
  map_mul' a b := by rw [map_mul, map_mul, MonoidHom.mul_apply]

/-- The unit reads off the generator of the given regular Borel character. -/
theorem borelCharacterUnit_val {A : Type v} [CommRing A] [Algebra K A]
    (chi : G.characters) (b : WithConv (G.borelAlgebra →ₐ[K] A)) :
    (borelCharacterUnit G chi b : A) =
      b.ofConv (borelCharacterMap G chi
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) := rfl

/-- The inverse character is the scalar on the associated one-dimensional fibre. -/
theorem borelCharacterUnit_inv_val {A : Type v} [CommRing A] [Algebra K A]
    (chi : G.characters) (b : WithConv (G.borelAlgebra →ₐ[K] A)) :
    (↑(borelCharacterUnit G chi b)⁻¹ : A) =
      b.ofConv (borelCharacterMap G chi
        (MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1)) := by
  exact DiagonalizableGroup.charOfPoint_apply_inv_coe
    ((AlgHom.mapDomain (borelCharacterMap G chi) b).ofConv) (Multiplicative.ofAdd 1)

/-- The inverse-character scaling is a regular polynomial action on the affine fibre. -/
def characterLineCoordinate (chi : G.characters) :
    SymmetricAlgebra K K →ₐ[K] G.borelAlgebra ⊗[K] SymmetricAlgebra K K :=
  SymmetricAlgebra.lift (LinearMap.toSpanSingleton K _
    (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1) ⊗ₜ[K]
      SymmetricAlgebra.ι K K 1))

/-- The regular action has inverse-character scalar over every coefficient algebra. -/
theorem characterLineCoordinate_eval {A : Type v} [CommRing A] [Algebra K A]
    (chi : G.characters) (b : WithConv (G.borelAlgebra →ₐ[K] A)) (a : A) :
    (Algebra.TensorProduct.lift b.ofConv
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm
        (Multiplicative.ofAdd a)).ofConv (fun _ _ => .all _ _)).comp
          (characterLineCoordinate G chi) =
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm
        (Multiplicative.ofAdd ((↑(borelCharacterUnit G chi b)⁻¹ : A) * a))).ofConv := by
  let f : SymmetricAlgebra K K →ₐ[K] A :=
    (Algebra.TensorProduct.lift b.ofConv
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm
        (Multiplicative.ofAdd a)).ofConv (fun _ _ => .all _ _)).comp
          (characterLineCoordinate G chi)
  let g : SymmetricAlgebra K K →ₐ[K] A :=
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm
      (Multiplicative.ofAdd ((↑(borelCharacterUnit G chi b)⁻¹ : A) * a))).ofConv
  have hgen : f (SymmetricAlgebra.ι K K 1) = g (SymmetricAlgebra.ι K K 1) := by
    simp only [f, g, AlgHom.comp_apply, characterLineCoordinate,
      SymmetricAlgebra.lift_ι_apply, LinearMap.toSpanSingleton_apply, one_smul,
      Algebra.TensorProduct.lift_tmul, AdditiveGroup.gaPointsMulEquiv_symm_apply_ι,
      toAdd_ofAdd]
    rw [← borelCharacterUnit_inv_val]
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  have hι : SymmetricAlgebra.ι K K x = x • SymmetricAlgebra.ι K K 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (map_smul (SymmetricAlgebra.ι K K) x (1 : K))
  change f (SymmetricAlgebra.ι K K x) = g (SymmetricAlgebra.ι K K x)
  rw [hι, map_smul, map_smul, hgen]

end SchubertGeometry.ProjectiveLine
