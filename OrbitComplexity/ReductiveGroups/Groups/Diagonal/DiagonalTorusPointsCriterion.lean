import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalMatrixTorus
import TauCeti.RingTheory.FiniteType.PointSeparation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Diagonal Torus Points Criterion

Diagonal field points of GL factor through the diagonal torus.
For a reduced finite-type target, field points detect the resulting
coordinate kernel inclusion. -/

noncomputable section
namespace ReductiveGroups

open WithConv TauCeti TauCeti.GeneralLinear

universe u
variable {K : Type u} [Field K] (n : ℕ)

/-- Every field-valued GL point with diagonal matrix is the image
of a point of the diagonal torus. This includes `n = 0`. -/
theorem diagonalTorusPoints_surjective_diagonal
    (g : WithConv (coordinateHopfAlgebra K n →ₐ[K] K))
    (v : Fin n → K)
    (hg : ((pointsMulEquiv n g : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.diagonal v) :
    ∃ t : WithConv
      (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[K] K),
      diagonalTorusPoints t = g := by
  classical
  let G := pointsMulEquiv n g
  have hu : IsUnit v := Matrix.isUnit_diagonal.mp (by
    rw [← hg]
    exact G.isUnit)
  let c : Fin n → Kˣ := MulEquiv.piUnits hu.unit
  have hc (i : Fin n) : (c i : K) = v i := by
    simp [c]
  let t : WithConv
      (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[K] K) :=
    (SplitTorus.pointsMulEquiv (R := K) (A := K)).symm
      (fun i => c i.down)
  refine ⟨t, ?_⟩
  apply (pointsMulEquiv (R := K) (A := K) n).injective
  rw [pointsMulEquiv_diagonalTorusPoints]
  have hcoord : diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t) = c := by
    funext i
    change (SplitTorus.pointsMulEquiv t) (ULift.up i) = c i
    rw [show t = (SplitTorus.pointsMulEquiv (R := K) (A := K)).symm
      (fun i => c i.down) from rfl, MulEquiv.apply_symm_apply]
  rw [hcoord]
  apply Units.ext
  ext i j
  rw [diagGL_apply, hg, Matrix.diagonal_apply]
  split_ifs <;> simp [hc]

/-- If every original field point has diagonal image in GL, the entire
diagonal-torus coordinate kernel lies in the coordinate kernel. Reducedness
is essential for upgrading pointwise vanishing to algebraic vanishing. -/
theorem DiagonalTorusCoordinateMap.ker_le_of_diagonal_points
    {B : Type u} [CommRing B] [HopfAlgebra K B]
    [Algebra.FiniteType K B] [IsReduced B] [IsAlgClosed K]
    (φ : coordinateHopfAlgebra K n →ₐc[K] B)
    (hdiag : ∀ p : B →ₐ[K] K,
      ∃ v : Fin n → K,
        ((pointsMulEquiv n
          (toConv (p.comp φ.toAlgHom)) : Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = Matrix.diagonal v)
    (a : coordinateHopfAlgebra K n)
    (ha : (diagonalTorusCoordinateMap (R := K) (N := n)).hom a = 0) :
    φ a = 0 := by
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro p
  obtain ⟨v, hv⟩ := hdiag p
  let g : WithConv (coordinateHopfAlgebra K n →ₐ[K] K) :=
    toConv (p.comp φ.toAlgHom)
  obtain ⟨t, ht⟩ := diagonalTorusPoints_surjective_diagonal n g v hv
  have hmap := MapPointsFunctor.diagonal_torus_app
    (R := K) (N := n) (CommAlgCat.of K K) t
  have heval := congrArg
    (fun q : WithConv (coordinateHopfAlgebra K n →ₐ[K] K) => q.ofConv a) hmap
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at heval
  have hzero : (diagonalTorusPoints t).ofConv a = 0 := by
    rw [← heval, ha, map_zero]
  have hp : p (φ a) = (diagonalTorusPoints t).ofConv a := by
    rw [ht]
    rfl
  rw [hp, hzero]
  exact (map_zero p).symm

end ReductiveGroups
