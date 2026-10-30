import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedWordClosure
import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedWordSeparatingFamily
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing

/-!
# Solvable Point Closure

Solvability passes from a subgroup of rational points to its reduced
closed subgroup, uniformly for every commutative value algebra. The proof
uses separation by the original point subgroup, not a density assertion
about all points of the closure. -/

noncomputable section
namespace ReductiveGroups
open TauCeti WithConv

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  (S : Subgroup (WithConv (B →ₐ[K] K)))

/-- A point `g` of the subgroup `S` of rational points, regarded as a rational point of the quotient
of `B` by the vanishing Hopf ideal of `S`. -/
def vanishingQuotientPoint (g : S) :
    WithConv (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
      (HopfIdeal.vanishingIdeal S) →ₐ[K] K) :=
  CommHopfAlgCat.liftQuotientPoint (CommHopfAlgCat.of K B)
    (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) g.val
    (fun b hb => (HopfIdeal.mem_vanishingIdeal S b).mp hb g)

/-- The equality is

```lean
(vanishingQuotientPoint S g).ofConv
      (Ideal.Quotient.mkₐ K (HopfIdeal.vanishingIdeal S).toIdeal b) = g.val.ofConv b
```
-/
theorem vanishingQuotientPoint_mk (g : S) (b : B) :
    (vanishingQuotientPoint S g).ofConv
      (Ideal.Quotient.mkₐ K (HopfIdeal.vanishingIdeal S).toIdeal b) = g.val.ofConv b :=
  rfl

/-- The equality is

```lean
a = 0
```
-/
theorem vanishingQuotientPoint_separates
    (a : CommHopfAlgCat.quotient (CommHopfAlgCat.of K B) (HopfIdeal.vanishingIdeal S))
    (ha : ∀ g : S, (vanishingQuotientPoint S g).ofConv a = 0) : a = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (HopfIdeal.vanishingIdeal S).toIdeal a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change b ∈ HopfIdeal.vanishingIdeal S
  apply (HopfIdeal.mem_vanishingIdeal S b).mpr
  intro g
  exact (vanishingQuotientPoint_mk S g b).symm.trans (ha g)

/-- The equality is

```lean
derivedGroupWord n x = 1
```
-/
theorem vanishingQuotient_derivedWord_identity
    (n : ℕ) (h : ∀ x : DerivedWordIndex n → S, derivedGroupWord n x = 1)
    {A : Type*} [CommRing A] [Algebra K A]
    (x : DerivedWordIndex n → WithConv
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
        (HopfIdeal.vanishingIdeal S) →ₐ[K] A)) : derivedGroupWord n x = 1 := by
  apply DerivedGroupWord.eq_one_of_separating_family
    (fun g : S => (vanishingQuotientPoint S g).ofConv)
    (vanishingQuotientPoint_separates S) n _ x
  intro y
  let q := CommHopfAlgCat.quotientPointsHom (CommHopfAlgCat.of K B)
    (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K)
  apply CommHopfAlgCat.quotientPointsHom_injective (CommHopfAlgCat.of K B)
    (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K)
  change q (derivedGroupWord n (fun i => vanishingQuotientPoint S (y i))) = q 1
  rw [derivedGroupWord_map q.hom, map_one]
  have hq : ∀ g : S, q (vanishingQuotientPoint S g) = g.val := by
    intro g
    exact CommHopfAlgCat.quotientPointsHom_liftQuotientPoint _ _ _ _ _
  simp only [hq]
  have hv := congrArg S.subtype (h y)
  simpa only [derivedGroupWord_map, Subgroup.coe_subtype, map_one] using hv

/-- For these parameters,

```lean
Group.IsSolvable (WithConv (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
      (HopfIdeal.vanishingIdeal S) →ₐ[K] A))
```
-/
theorem vanishingQuotient_points_isSolvable [Group.IsSolvable S]
    {A : Type*} [CommRing A] [Algebra K A] :
    Group.IsSolvable (WithConv (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
      (HopfIdeal.vanishingIdeal S) →ₐ[K] A)) := by
  obtain ⟨n, hn⟩ := DerivedWordSolvability.exists_identity_of_isSolvable (G := S)
  exact isSolvable_of_derivedGroupWord_identity n
    (vanishingQuotient_derivedWord_identity S n hn)

end ReductiveGroups
