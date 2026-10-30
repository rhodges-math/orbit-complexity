import OrbitComplexity.ReductiveGroups.GLn.Points
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalTorusPointsCriterion
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusSplitPresentation
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# The diagonal torus is a maximal torus of `GL_n`

The quotient of `O(GL_n)` by the diagonal-torus ideal is isomorphic, through restriction of
functions, to the Laurent polynomial ring `K[ℤⁿ]`; hence the diagonal subgroup is a split torus.

Over an algebraically closed field it is maximal. Let `T'` be a torus containing the diagonal
torus `D`. Then `T'` is reduced and commutative, so every point of `T'` commutes with every
invertible diagonal matrix, and a matrix commuting with all invertible diagonal matrices is
diagonal (the centralizer of `D` in `GL_n` is `D`). Hence `T'(K) ⊆ D(K)`, and the Nullstellensatz
for the reduced coordinate ring of `T'` gives `T' = D`.

## Main declarations

* `ReductiveGroups.GLn.torusIdeal_quotient_torus`: the diagonal subgroup is a torus.
* `ReductiveGroups.GLn.eq_diagonal_of_forall_commute`: the centralizer of the diagonal torus.
* `ReductiveGroups.GLn.isMaximalTorus_torusIdeal`: the diagonal torus is a maximal torus.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.5 and Example 11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§16.1 and 19.
* J. S. Milne, *Algebraic Groups* (2017), Example 12.6 and §17.a.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §§3.2 and 7.1.
-/

noncomputable section
namespace ReductiveGroups.GLn

open TauCeti TauCeti.GeneralLinear CategoryTheory WithConv

universe u

section Torus

variable (K : Type u) [Field K] (n : ℕ)

/-- Restriction of functions identifies the quotient by the diagonal-torus ideal with the
Laurent polynomial ring of the split torus. -/
def torusQuotientIso :
    FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra K n) (torusIdeal K n) ≅
      DiagonalizableGroup.coordinateRing K (SplitTorus.characterGroup (ULift.{u} (Fin n))) :=
  ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk
    (HopfIdeal.kerLiftBialgEquiv (torusRestriction K n) (torusRestriction_surjective K n)))

/-- The diagonal subgroup of `GL_n` is a split torus. -/
theorem torusIdeal_quotient_splitTorus :
    splitTorusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra K n)
        (torusIdeal K n)) :=
  (splitTorusCommHopfAlgProperty K).prop_of_iso (torusQuotientIso K n).symm
    (SplitTorus.splitTorus_coordinateRing K _)

/-- The diagonal subgroup of `GL_n` is a torus. -/
theorem torusIdeal_quotient_torus :
    torusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra K n)
        (torusIdeal K n)) :=
  splitTorusCommHopfAlgProperty.torus K _ (torusIdeal_quotient_splitTorus K n)

variable {K n}

/-- A matrix commuting with every invertible diagonal matrix is diagonal, provided the field has
an element other than `0` and `1`. -/
theorem eq_diagonal_of_forall_commute {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (g : GL (Fin n) K)
    (hg : ∀ t : Fin n → Kˣ, g * diagGL t = diagGL t * g) :
    (g : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun i => (g : Matrix (Fin n) (Fin n) K) i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hab]
    let t : Fin n → Kˣ := Function.update 1 a (Units.mk0 c hc0)
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K) a b) (hg t)
    simp only [Units.val_mul] at h
    have hdiag : ((diagGL t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.diagonal fun i => (t i : K) := by
      ext i j
      rw [diagGL_apply, Matrix.diagonal_apply]
    rw [hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hta : (t a : K) = c := by simp [t]
    have htb : (t b : K) = 1 := by simp [t, Ne.symm hab]
    rw [hta, htb, mul_one] at h
    have h2 : (c - 1) * (g : Matrix (Fin n) (Fin n) K) a b = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hc1
    · exact h3

/-- Invertible diagonal matrices are points of the diagonal torus. -/
theorem diagonal_mem_matrixPoints_torusIdeal (D : GL (Fin n) K) (v : Fin n → K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal v) :
    D ∈ matrixPoints (torusIdeal K n) K := by
  rw [mem_matrixPoints_iff (torusIdeal K n)]
  intro x hx
  have hv : ((pointsMulEquiv n ((pointsMulEquiv (R := K) (A := K) n).symm D) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.diagonal v := by
    rw [MulEquiv.apply_symm_apply, hD]
  obtain ⟨t, ht⟩ := diagonalTorusPoints_surjective_diagonal n _ v hv
  have hmap := MapPointsFunctor.diagonal_torus_app
    (R := K) (N := n) (CommAlgCat.of K K) t
  have heval := congrArg
    (fun q : WithConv (coordinateHopfAlgebra K n →ₐ[K] K) => q.ofConv x) hmap
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at heval
  have hπ : torusRestriction K n x = 0 :=
    (torusRestriction_eq_zero_iff K n x).mpr ((HopfIdeal.mem_toIdeal).mpr hx)
  rw [← ht]
  change t.ofConv (torusRestriction K n x) = _ at heval
  rw [← heval, hπ, map_zero]

end Torus

section Maximal

variable (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)

/-- A torus containing the diagonal torus equals it. -/
theorem torusIdeal_le_of_torus (J : HopfIdeal K (coordinateHopfAlgebra K n))
    (hJ : torusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra K n) J))
    (hle : J ≤ torusIdeal K n) : torusIdeal K n ≤ J := by
  classical
  -- The competing torus is split, hence reduced and cocommutative.
  have hsplit := torus_split_of_isAlgClosed _ hJ
  obtain ⟨m, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff K _).mp hsplit
  have hred : IsReduced (coordinateHopfAlgebra K n ⧸ J.toIdeal) := by
    let f := FiniteTypeCommHopfAlgCat.toBialgHom e.inv
    have hf : Function.Injective f := (ConcreteCategory.bijective_of_isIso e.inv).1
    have hdom : IsDomain (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) :=
      inferInstance
    exact isReduced_of_injective f.toAlgHom.toRingHom hf
  have hrad : J.toIdeal.IsRadical := (Ideal.isRadical_iff_quotient_reduced _).mpr hred
  have hcocomm : Coalgebra.IsCocomm K
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra K n) J) :=
    torusCommHopfAlgProperty.isCocomm K _ hJ
  have hcommS := @CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup K _
    (coordinateHopfAlgebra K n) J hcocomm (CommAlgCat.of K K)
  -- Points of the competing torus commute with each other.
  have hcomm : ∀ g h : GL (Fin n) K, g ∈ matrixPoints J K → h ∈ matrixPoints J K →
      g * h = h * g := by
    intro g h hg hh
    have hab := hcommS.is_comm.comm
      (⟨(pointsMulEquiv n).symm g, hg⟩ : CommHopfAlgCat.quotientPointsSubgroup
        (coordinateHopfAlgebra K n) J (CommAlgCat.of K K))
      ⟨(pointsMulEquiv n).symm h, hh⟩
    have hab' := congrArg Subtype.val hab
    simp only [Subgroup.coe_mul] at hab'
    apply (pointsMulEquiv (R := K) (A := K) n).symm.injective
    rw [map_mul, map_mul]
    exact hab'
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  intro x hx
  rw [← HopfIdeal.mem_toIdeal]
  apply mem_of_forall_algHom_of_isRadical (k := K) (K := K) J.toIdeal hrad
  intro f hf
  let g := pointsMulEquiv n (toConv f)
  have hg : g ∈ matrixPoints J K :=
    (pointsMulEquiv_mem_matrixPoints_iff J _).mpr
      (fun y hy => hf ((HopfIdeal.mem_toIdeal).mpr hy))
  have hgdiag := eq_diagonal_of_forall_commute hc.1 hc.2 g (fun t => hcomm g (diagGL t) hg
    (matrixPoints_antitone hle (diagonal_mem_matrixPoints_torusIdeal (diagGL t)
      (fun i => (t i : K)) (by ext i j; rw [diagGL_apply, Matrix.diagonal_apply]))))
  have hgT := diagonal_mem_matrixPoints_torusIdeal g _ hgdiag
  rw [pointsMulEquiv_mem_matrixPoints_iff] at hgT
  exact hgT x hx

/-- **The diagonal torus is a maximal torus of `GL_n` over an algebraically closed field.** -/
theorem isMaximalTorus_torusIdeal :
    HopfIdeal.IsMaximalTorus K (coordinateHopfAlgebra K n) (torusIdeal K n) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  exact ⟨torusIdeal_quotient_torus K n, fun J hJ hle => torusIdeal_le_of_torus K n J hJ hle⟩

end Maximal

end GLn
