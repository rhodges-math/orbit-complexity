/-
Adapted from TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus,
Copyright (c) 2026 The Tau Ceti contributors. Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentCharacters
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Diagonal Matrix Torus

The concrete diagonal torus in the existing general-linear coordinate Hopf algebra. -/
open CategoryTheory WithConv TauCeti TauCeti.GeneralLinear
open scoped CategoryTheory.MonObj
namespace ReductiveGroups

universe u w w'

variable {R : Type u} [CommRing R] {N : ℕ}

/-- Diagonal invertible matrices, adapted from Tau Ceti's diagonal-matrix construction. -/
def diagGL {k : Type*} [Semiring k] {idx : Type*} [Fintype idx] [DecidableEq idx] :
    (idx → kˣ) →* Matrix.GeneralLinearGroup idx k :=
  (Units.map (Matrix.diagonalRingHom idx k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The equality is

```lean
diagGL t i j = if i = j then (t i : k) else 0
```
-/
@[simp] theorem diagGL_apply {k : Type*} [Semiring k] {idx : Type*} [Fintype idx]
    [DecidableEq idx] (t : idx → kˣ) (i j : idx) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  change (Matrix.diagonal fun i => (t i : k)) i j = _
  exact Matrix.diagonal_apply ..

/-- The equality is

```lean
Function.Injective (diagGL (k := k) (idx := idx))
```
-/
theorem diagGL_injective {k : Type*} [Semiring k] {idx : Type*} [Fintype idx]
    [DecidableEq idx] : Function.Injective (diagGL (k := k) (idx := idx)) := by
  intro t s h
  funext i
  apply Units.ext
  have := congrArg (fun g : Matrix.GeneralLinearGroup idx k => (g : Matrix idx idx k) i i) h
  simpa using this

/-- The equality is

```lean
Matrix.GeneralLinearGroup.map f (diagGL t) =
      diagGL fun i => Units.map (f : k →* S) (t i)
```
-/
@[simp] theorem map_diagGL {k S : Type*} [CommRing k] [CommRing S]
    {idx : Type*} [Fintype idx] [DecidableEq idx]
    (f : k →+* S) (t : idx → kˣ) :
    Matrix.GeneralLinearGroup.map f (diagGL t) =
      diagGL fun i => Units.map (f : k →* S) (t i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, Units.coe_map,
      MonoidHom.coe_ofClass]
  split_ifs <;> simp

/-- Restrict a same-universe coordinate family on `ULift (Fin N)` to the canonical copy of
`Fin N`.  The universe lift is required only by the current same-universe group-scheme API. -/
def diagonalTorusCoordinates {A : Type w} [Monoid A] :
    (ULift.{u} (Fin N) → Aˣ) →* (Fin N → Aˣ) where
  toFun t i := t (ULift.up i)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restricting a universe-lifted coordinate family evaluates it at the canonical lift. -/
@[simp]
theorem diagonalTorusCoordinates_apply {A : Type w} [Monoid A]
    (t : ULift.{u} (Fin N) → Aˣ) (i : Fin N) :
    diagonalTorusCoordinates t i = t (ULift.up i) :=
  (rfl)

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The diagonal-torus homomorphism on `A`-points.  Under the split-torus and general-linear
points equivalences it is the diagonal embedding `diagGL : (Fin N → Aˣ) →* GL (Fin N) A`. -/
noncomputable def diagonalTorusPoints :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp
    ((diagGL (k := A)).comp
      ((diagonalTorusCoordinates (N := N) (A := A)).comp
        (SplitTorus.pointsMulEquiv (R := R) (A := A)).toMonoidHom))

-- Not `@[simp]`: `pointsMulEquiv_apply` already simplifies the left-hand side, so `simpNF`
-- rejects this higher-level equation as not being in normal form.
/-- Reading the image of a split-torus point as an invertible matrix gives the diagonal matrix
whose diagonal entries are the coordinates of that point.

The equality is

```lean
pointsMulEquiv N (diagonalTorusPoints f) =
      diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv f))
```
-/
theorem pointsMulEquiv_diagonalTorusPoints
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A)) :
    pointsMulEquiv N (diagonalTorusPoints f) =
      diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv f)) := by
  simp [diagonalTorusPoints]

/-- The diagonal-torus homomorphism on points is injective. -/
theorem diagonalTorusPoints_injective :
    Function.Injective (diagonalTorusPoints (R := R) (N := N) (A := A)) := by
  intro f g h
  have hdiag :
      diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv f)) =
        diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv g)) := by
    rw [← pointsMulEquiv_diagonalTorusPoints, ← pointsMulEquiv_diagonalTorusPoints, h]
  have hcoordinates := diagGL_injective hdiag
  apply (SplitTorus.pointsMulEquiv (R := R) (A := A)).injective
  funext i
  simpa only [diagonalTorusCoordinates, MonoidHom.coe_mk, OneHom.coe_mk, ULift.up_down] using
    congrFun hcoordinates i.down

variable {B : Type w'} [CommRing B] [Algebra R B]

-- Not `@[simp]`: `AlgHom.mapValue_apply` already simplifies the left-hand side, so `simpNF`
-- rejects this higher-level equation as not being in normal form.
/-- The diagonal embedding is natural in the value algebra.

The equality is

```lean
AlgHom.mapValue (H := coordinateHopfAlgebra R N) phi (diagonalTorusPoints f) =
      diagonalTorusPoints
        (AlgHom.mapValue
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) phi f)
```
-/
theorem mapValue_diagonalTorusPoints (phi : A →ₐ[R] B)
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R N) phi (diagonalTorusPoints f) =
      diagonalTorusPoints
        (AlgHom.mapValue
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) phi f) := by
  apply (pointsMulEquiv (R := R) (A := B) N).injective
  rw [pointsMulEquiv_mapValue N phi (diagonalTorusPoints f),
    pointsMulEquiv_diagonalTorusPoints, pointsMulEquiv_diagonalTorusPoints, map_diagGL]
  exact congrArg diagGL
    (funext fun i ↦ (SplitTorus.pointsMulEquiv_mapValue phi f (ULift.up i)).symm)

end Points

section Functor

/-- The natural transformation of group-valued functors whose component sends a coordinate
family of units to the corresponding diagonal invertible matrix. -/
noncomputable def diagonalTorusPointsMap :
    HopfAlgebra.pointsFunctor
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N) where
  app A := GrpCat.ofHom (diagonalTorusPoints (A := A))
  naturality _ _ phi := by
    ext f
    exact (mapValue_diagonalTorusPoints phi.hom f).symm

/-- The component of the natural diagonal-torus map at a value algebra is
`diagonalTorusPoints`. -/
@[simp]
theorem diagonalTorusPointsMap_app (A : CommAlgCat.{w} R) :
    (diagonalTorusPointsMap (R := R) (N := N)).app A =
      GrpCat.ofHom diagonalTorusPoints :=
  (rfl)

end Functor

section Scheme

/-- The coordinate morphism of the diagonal torus, recovered from its natural action on points.
Its direction is opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R N ⟶
      _root_.CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) :=
  CommHopfAlgCat.homOfPointsMap
    (H := _root_.CommHopfAlgCat.of R
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
    (K := coordinateHopfAlgebra R N)
    (diagonalTorusPointsMap.{u, u} (R := R) (N := N))

/-- Precomposition by the diagonal-torus coordinate morphism is the previously constructed
natural map on convolution points. -/
theorem MapPointsFunctor.diagonal_torus :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (diagonalTorusCoordinateMap (R := R) (N := N)) :
      HopfAlgebra.pointsFunctor
          (R := R)
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N)) =
      (diagonalTorusPointsMap.{u, u} (R := R) (N := N) :
        HopfAlgebra.pointsFunctor
            (R := R)
            (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
          HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N)) :=
  CommHopfAlgCat.mapPointsFunctor_homOfPointsMap _

/-- On every value algebra, the map induced by the diagonal-torus coordinate morphism is
`diagonalTorusPoints`. -/
@[simp]
theorem MapPointsFunctor.diagonal_torus_app
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points
      (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (diagonalTorusCoordinateMap (R := R) (N := N))).app A f =
      diagonalTorusPoints f := by
  -- Transport the same-universe computation at the generic point `id_K` to `f` by naturality.
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))
  let p : WithConv (K →ₐ[R] K) := toConv (AlgHom.id R K)
  have hp :
      (CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := R) (N := N))).app (CommAlgCat.of R K) p =
        diagonalTorusPoints p := by
    rw [MapPointsFunctor.diagonal_torus, diagonalTorusPointsMap_app]
    exact GrpCat.ofHom_apply diagonalTorusPoints p
  have hfp : AlgHom.mapValue (H := K) f.ofConv p = f := by
    simp only [AlgHom.mapValue_apply, p, AlgHom.comp_id, WithConv.toConv_ofConv]
  have hnat :
      AlgHom.mapValue (H := coordinateHopfAlgebra R N) f.ofConv
          ((CommHopfAlgCat.mapPointsFunctor
            (diagonalTorusCoordinateMap (R := R) (N := N))).app (CommAlgCat.of R K) p) =
        (CommHopfAlgCat.mapPointsFunctor
          (diagonalTorusCoordinateMap (R := R) (N := N))).app A
            (AlgHom.mapValue (H := K) f.ofConv p) := by
    exact DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain
        (diagonalTorusCoordinateMap (R := R) (N := N)).hom f.ofConv) p
  rw [← hfp, ← hnat, hp, mapValue_diagonalTorusPoints]

/-- The diagonal-torus coordinate morphism sends a generic matrix entry to the corresponding
coordinate character on the diagonal, and to zero off the diagonal. -/
@[simp]
theorem diagonalTorusCoordinateMap_X (i j : Fin N) :
    (diagonalTorusCoordinateMap (R := R) (N := N)).hom
        (coordinateHopfAlgebraAlgEquiv R N
          (coordinateRingMap R N (MvPolynomial.X (i, j)))) =
      if i = j then
        MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1
      else 0 := by
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))
  let p : WithConv (K →ₐ[R] K) := toConv (AlgHom.id R K)
  have hpoints := MapPointsFunctor.diagonal_torus_app
    (R := R) (N := N) (CommAlgCat.of R K) p
  have heval := congrArg
    (fun q : WithConv (coordinateHopfAlgebra R N →ₐ[R] K) ↦ q.ofConv
      (coordinateHopfAlgebraAlgEquiv R N
        (coordinateRingMap R N (MvPolynomial.X (i, j))))) hpoints
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at heval
  have hdiag := congrArg
    (fun g : Matrix.GeneralLinearGroup (Fin N) K ↦ g i j)
      (pointsMulEquiv_diagonalTorusPoints p)
  rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, diagGL_apply,
    diagonalTorusCoordinates_apply, SplitTorus.pointsMulEquiv_apply_coe] at hdiag
  have h := heval.trans hdiag
  dsimp only [p, WithConv.toConv_ofConv, AlgHom.id_apply] at h
  exact h

/-- The diagonal-torus coordinate morphism is onto: diagonal entries and their Hopf antipodes
generate all Laurent characters. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap (R := R) (N := N)).hom := by
  classical
  let φ := (diagonalTorusCoordinateMap (R := R) (N := N)).hom
  let H : AddSubgroup (ULift.{u} (Fin N) →₀ ℤ) := {
    carrier := {m | ∃ b, φ b = MonoidAlgebra.single (Multiplicative.ofAdd m) 1}
    zero_mem' := by
      refine ⟨1, ?_⟩
      exact (map_one φ).trans MonoidAlgebra.one_def
    add_mem' := by
      rintro a b ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x * y, ?_⟩
      simp [map_mul, hx, hy, MonoidAlgebra.single_mul_single]
    neg_mem' := by
      rintro a ⟨x, hx⟩
      refine ⟨HopfAlgebra.antipode R x, ?_⟩
      rw [BialgHomClass.map_antipode, hx, MonoidAlgebra.antipode_single]
      simp
  }
  have hgen (i : ULift.{u} (Fin N)) : Finsupp.single i (1 : ℤ) ∈ H := by
    refine ⟨TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv R N
      (TauCeti.GeneralLinear.coordinateRingMap R N
        (MvPolynomial.X (i.down, i.down))), ?_⟩
    simpa [φ] using diagonalTorusCoordinateMap_X (R := R) (N := N) i.down i.down
  have hsingle (i : ULift.{u} (Fin N)) (z : ℤ) : Finsupp.single i z ∈ H := by
    have hz := H.zsmul_mem (hgen i) z
    simpa using hz
  have hall (m : ULift.{u} (Fin N) →₀ ℤ) : m ∈ H := by
    induction m using Finsupp.induction with
    | zero => exact H.zero_mem
    | @single_add i z m _ _ ih => exact H.add_mem (hsingle i z) ih
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of m => exact hall m.toAdd
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | smul r x hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨r • a, by rw [map_smul, ha]⟩

end Scheme

section Tangent

variable {K : Type u} [Field K] {n : ℕ}

/-- The differential of the diagonal torus has diagonal matrix values. -/
theorem diagonalTorus_tangentMatrix_apply
    (d : Derivation K
      (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
      (Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) K))
    (i j : Fin n) :
    TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K)
        (diagonalTorusCoordinateMap (R := K) (N := n)).hom d) i j =
      if i = j then
        Bialgebra.CounitAlgebra.algEquivSelf K
          (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) K
          (d (MonoidAlgebra.single
            (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1))
      else 0 := by
  rw [TauCeti.GeneralLinear.tangentMatrix_apply,
    TauCeti.algEquivSelf_derivationComp_apply]
  change (Bialgebra.CounitAlgebra.algEquivSelf K
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) K)
      (d ((diagonalTorusCoordinateMap (R := K) (N := n)).hom
        (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))))) = _
  rw [diagonalTorusCoordinateMap_X]
  split_ifs <;> simp <;> rfl

/-- Every diagonal matrix occurs as the image of a tangent vector of the diagonal
torus. This includes the empty-index case. -/
theorem DiagonalTorus.tangentMatrix_surjective_diagonal
    (v : Fin n → K) :
    ∃ d : Derivation K
      (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
      (Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) K),
      TauCeti.GeneralLinear.tangentMatrix n
        (TauCeti.derivationComp (B := K)
          (diagonalTorusCoordinateMap (R := K) (N := n)).hom d) =
        Matrix.diagonal v := by
  let ψ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative K :=
    (TauCeti.freeAbelianCharEquiv (M := Multiplicative K)).symm
      (fun i => Multiplicative.ofAdd (v i.down))
  refine ⟨diagonalizableTangentOfAdditive ψ, ?_⟩
  ext i j
  rw [diagonalTorus_tangentMatrix_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst j
    change characterDifferential (K := K)
      (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1))
      (diagonalizableTangentOfAdditive ψ) = v i
    rw [CharacterDifferential.of_additive_tangent]
    simp [ψ]
  · rfl

end Tangent
end ReductiveGroups


