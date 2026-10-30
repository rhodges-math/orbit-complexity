import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularIdeal
import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularGroup
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Closed subgroups of `GL_n` through their matrix points

A Hopf ideal `Q` of `O(GL_n)` cuts out, over every commutative algebra `A`, a subgroup of
`GL_n(A)`: the invertible matrices whose evaluation kills `Q`. It is the image of the point group
of the quotient Hopf algebra `O(GL_n)/Q`, which maps onto it injectively.

When `O(GL_n)/Q` is reduced, the Nullstellensatz recovers `Q` from these points with values in
an algebraically closed field: a function vanishing on all of them lies in `Q`. This is the tool
used below to compare closed subgroups of `GL_n` through their matrix points.

## Main declarations

* `ReductiveGroups.GLn.matrixPoints`: the matrix points of the closed subgroup cut out by `Q`.
* `ReductiveGroups.GLn.quotientMatrixHom`: the isomorphism from the point group of `O(GL_n)/Q` onto
  its matrix points.
* `ReductiveGroups.GLn.mem_of_forall_algHom_of_isRadical`: membership in a radical ideal detected at
  algebraically closed points.
* `ReductiveGroups.GLn.matrixPoints_upperTriangularIdeal`: the matrix points of the upper-triangular
  subgroup are the invertible upper-triangular matrices.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), AG.§3 and §1.
* J. S. Milne, *Algebraic Groups* (2017), §§1.a, 1.c and Appendix A.
* The Stacks Project, Tag 00FV (Hilbert Nullstellensatz).
-/

noncomputable section
namespace ReductiveGroups.GLn

open TauCeti TauCeti.GeneralLinear CategoryTheory WithConv

universe u w

section Separation

variable {k A K : Type*} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  [Field K] [Algebra k K] [IsAlgClosed K]

/-- An element of a finite-type algebra over a field lies in a radical ideal as soon as it
vanishes at every point with values in an algebraically closed extension that kills the
ideal. -/
theorem mem_of_forall_algHom_of_isRadical (I : Ideal A) (hI : I.IsRadical) {x : A}
    (h : ∀ f : A →ₐ[k] K, I ≤ RingHom.ker f.toRingHom → f x = 0) : x ∈ I :=
  hI ((TauCeti.mem_radical_iff_forall_algHom_apply_eq_zero (k := k) (K := K) I x).mpr h)

end Separation

section MatrixPoints

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The matrix points over `A` of the closed subgroup of `GL_n` cut out by a Hopf ideal. -/
def matrixPoints (Q : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w) [CommRing A]
    [Algebra R A] : Subgroup (GL (Fin n) A) :=
  (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n) Q
    (CommAlgCat.of R A)).comap (pointsMulEquiv (R := R) (A := A) n).symm.toMonoidHom

variable (Q : HopfIdeal R (coordinateHopfAlgebra R n)) {A : Type w} [CommRing A] [Algebra R A]

/-- The equivalence is

```lean
g ∈ matrixPoints Q A ↔ ∀ x ∈ Q, ((pointsMulEquiv n).symm g).ofConv x = 0
```
-/
theorem mem_matrixPoints_iff (g : GL (Fin n) A) :
    g ∈ matrixPoints Q A ↔ ∀ x ∈ Q, ((pointsMulEquiv n).symm g).ofConv x = 0 :=
  CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _

/-- The equivalence is

```lean
pointsMulEquiv n p ∈ matrixPoints Q A ↔ ∀ x ∈ Q, p.ofConv x = 0
```
-/
theorem pointsMulEquiv_mem_matrixPoints_iff
    (p : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv n p ∈ matrixPoints Q A ↔ ∀ x ∈ Q, p.ofConv x = 0 := by
  rw [mem_matrixPoints_iff, MulEquiv.symm_apply_apply]

/-- The inclusion is

```lean
matrixPoints Q' A ≤ matrixPoints Q A
```
-/
theorem matrixPoints_antitone {Q Q' : HopfIdeal R (coordinateHopfAlgebra R n)} (h : Q ≤ Q') :
    matrixPoints Q' A ≤ matrixPoints Q A := by
  intro g hg
  rw [mem_matrixPoints_iff] at hg ⊢
  exact fun x hx => hg x (h hx)

variable (A) in
/-- The point group of the quotient `O(GL_n)/Q`, mapped to matrices. -/
def quotientMatrixHom :
    WithConv ((coordinateHopfAlgebra R n ⧸ Q.toIdeal) →ₐ[R] A) →* matrixPoints Q A where
  toFun q := ⟨pointsMulEquiv n
      ((CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R n) Q (CommAlgCat.of R A)).hom
        q),
    (pointsMulEquiv_mem_matrixPoints_iff Q _).mpr
      ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp
        (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _))⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]

/-- The map is injective:

```lean
Function.Injective (quotientMatrixHom Q A)
```
-/
theorem quotientMatrixHom_injective :
    Function.Injective (quotientMatrixHom Q A) := by
  intro a b h
  have h' := congrArg Subtype.val h
  simp only [quotientMatrixHom, MonoidHom.coe_mk, OneHom.coe_mk] at h'
  exact CommHopfAlgCat.quotientPointsHom_injective _ _ _ ((pointsMulEquiv n).injective h')

/-- The map is surjective:

```lean
Function.Surjective (quotientMatrixHom Q A)
```
-/
theorem quotientMatrixHom_surjective :
    Function.Surjective (quotientMatrixHom Q A) := by
  rintro ⟨g, hg⟩
  have hg' : (pointsMulEquiv n).symm g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopfAlgebra R n) Q (CommAlgCat.of R A) := hg
  obtain ⟨q, hq⟩ := hg'
  refine ⟨q, Subtype.ext ?_⟩
  simp only [quotientMatrixHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [hq, MulEquiv.apply_symm_apply]

/-- A solvable point group of `O(GL_n)/Q` has solvable matrix points. -/
theorem isSolvable_matrixPoints
    [Group.IsSolvable (WithConv ((coordinateHopfAlgebra R n ⧸ Q.toIdeal) →ₐ[R] A))] :
    Group.IsSolvable (matrixPoints Q A) :=
  Group.isSolvable_of_surjective (quotientMatrixHom_surjective Q)

/-- Solvable matrix points give a solvable point group of `O(GL_n)/Q`. -/
theorem isSolvable_quotientPoints [Group.IsSolvable (matrixPoints Q A)] :
    Group.IsSolvable (WithConv ((coordinateHopfAlgebra R n ⧸ Q.toIdeal) →ₐ[R] A)) :=
  Group.isSolvable_of_isSolvable_injective (quotientMatrixHom_injective Q)

variable (R A) in
/-- The matrix points of the upper-triangular subgroup are the invertible upper-triangular
matrices. -/
theorem matrixPoints_upperTriangularIdeal :
    matrixPoints (upperTriangularIdeal R n) A = upperTriangularGroup A n := by
  ext g
  rw [mem_upperTriangularGroup_iff]
  have h := GLn.UpperTriangularIdeal.mem_upperTriangularIdeal_iff R n (CommAlgCat.of R A)
    ((pointsMulEquiv n).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

end MatrixPoints

end GLn
