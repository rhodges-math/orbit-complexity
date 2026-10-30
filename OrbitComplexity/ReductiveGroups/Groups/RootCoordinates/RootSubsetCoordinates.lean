import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.RootSubsetIdeal
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial coordinates on closed root-support groups

Ordered multiplication of root subgroups identifies each closed root-support quotient
with a polynomial algebra. The kernel calculation uses the exact rational-point subgroup.
-/

noncomputable section
namespace ReductiveGroups.BorelRootSubset
open TauCeti
universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

private abbrev Tangent (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

variable (I J : HopfIdeal K B) (hJI : J ≤ I)
  (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
  (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
  (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
  (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
  (e : Module.Basis (borelRootCharacterIndex J π) K (Tangent J π hπ))
  (he : ∀ i, (e i).val = gaAffineGroupTangent (x i))
  (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
  (S : Set (borelRootCharacterIndex J π)) (hS : IsBorelRootCharacterClosed J π S)

omit [Finite ι] in
include he in
private theorem tangent_mem (i : borelRootCharacterIndex J π) :
    gaAffineGroupTangent (x i) ∈ Tangent J π hπ := he i ▸ (e i).property

include hJI hI hJ hker hB he hx

private theorem product_mem (l : List S) (a : S → K) :
    borelRootSubsetProduct J π hπ x (tangent_mem J π hπ x e he) S l a ∈
      borelRootSubsetSubgroup I J hJI hI hJ π hπ hker hB x e he hx S hS := by
  exact borelRootSubsetProduct_mem I J hJI hI hJ π hπ hker hB x e he hx
    (tangent_mem J π hπ x e he) hS l a

private theorem coordinate_surjective (l : List S) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Function.Surjective (gaProductCoordinate (fun i : S => x i.val) l) := by
  obtain ⟨F, hF⟩ := exists_borelRootSubset_polynomialEquiv I J hJI hI hJ π hπ hker hB
    x e he hx S l hl hall
  let L := borelRootLogarithmCoordinateMap J hJ π hπ (fun i : S => e.coord i.val)
  have hcomp : (gaProductCoordinate (fun i : S => x i.val) l).comp L = F.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change gaProductCoordinate (fun i : S => x i.val) l (L (MvPolynomial.X i)) =
      F (MvPolynomial.X i)
    rw [show L (MvPolynomial.X i) =
      borelRootLogarithmCoordinate J hJ π hπ (e.coord i.val) by
        exact MvPolynomial.aeval_X _ _]
    exact (hF i).symm
  intro p
  refine ⟨L (F.symm p), ?_⟩
  exact (DFunLike.congr_fun hcomp (F.symm p)).trans (F.apply_symm_apply p)

private theorem coordinate_ker (l : List S) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    RingHom.ker (gaProductCoordinate (fun i : S => x i.val) l).toRingHom =
      (ideal I J hJI hI hJ π hπ hker hB x e he hx S hS).toIdeal := by
  ext b
  change gaProductCoordinate (fun i : S => x i.val) l b = 0 ↔
    b ∈ ideal I J hJI hI hJ π hπ hker hB x e he hx S hS
  constructor
  · intro hb
    apply (HopfIdeal.mem_vanishingIdeal _ _).mpr
    intro g
    obtain ⟨u, hu, hval⟩ := Subgroup.mem_map.mp g.property
    obtain ⟨a, ha⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB
      x e he hx (tangent_mem J π hπ x e he) hS l hl hall u hu
    have hprod : (borelRootSubsetProduct J π hπ x
        (tangent_mem J π hπ x e he) S l a).val = g.val :=
      (congrArg Subtype.val ha).trans hval
    have hev := DFunLike.congr_fun
      (gaProductCoordinate_eval (fun i : S => x i.val) l a) b
    change MvPolynomial.aeval a (gaProductCoordinate (fun i : S => x i.val) l b) =
      ((borelRootSubsetProduct J π hπ x
        (tangent_mem J π hπ x e he) S l a).val.ofConv) b at hev
    rw [hb, map_zero, hprod] at hev
    exact hev.symm
  · intro hb
    apply MvPolynomial.funext
    intro a
    rw [map_zero]
    have hmem := product_mem I J hJI hI hJ π hπ hker hB x e he hx S hS l a
    have hzero := (HopfIdeal.mem_vanishingIdeal _ _).mp hb
      ⟨_, Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩⟩
    have hev := DFunLike.congr_fun
      (gaProductCoordinate_eval (fun i : S => x i.val) l a) b
    exact hev.trans hzero

/-- Ordered root multiplication identifies the root-support quotient with a polynomial algebra. -/
def coordinateEquiv (l : List S) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (B ⧸ (ideal I J hJI hI hJ π hπ hker hB x e he hx S hS).toIdeal) ≃ₐ[K]
      MvPolynomial S K :=
  (Ideal.quotientEquivAlgOfEq K
    (coordinate_ker I J hJI hI hJ π hπ hker hB x e he hx S hS l hl hall).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (coordinate_surjective I J hJI hI hJ π hπ hker hB x e he hx S l hl hall))

/-- On coordinate classes the polynomial chart is the pullback of ordered multiplication. -/
theorem coordinateEquiv_mk (l : List S) (hl : l.Nodup) (hall : ∀ i, i ∈ l) (b : B) :
    coordinateEquiv I J hJI hI hJ π hπ hker hB x e he hx S hS l hl hall
      (Ideal.Quotient.mk _ b) = gaProductCoordinate (fun i : S => x i.val) l b := by
  rfl

end ReductiveGroups.BorelRootSubset
