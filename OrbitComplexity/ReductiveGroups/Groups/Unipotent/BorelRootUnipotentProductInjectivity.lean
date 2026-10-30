import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypePointTangentRigidity
import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentTorusIntersection
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusCoordinateMap

/-!
# Borel Root Unipotent Product Injectivity

The torus and the Ga-only Borel subgroup have trivial
scheme-theoretic intersection, hence their point-product is injective
over every commutative value algebra. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

universe u v
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The equality is

```lean
I ⊔ borelRootUnipotentHopfIdeal J π hπ =
      HopfIdeal.augmentation K B
```
-/
theorem BorelRootUnipotent.torus_sup_eq_augmentation
    (I J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal) :
    I ⊔ borelRootUnipotentHopfIdeal J π hπ =
      HopfIdeal.augmentation K B := by
  let U := borelRootUnipotentHopfIdeal J π hπ
  let T := I ⊔ U
  let H := CommHopfAlgCat.of K B
  let Q := CommHopfAlgCat.quotient H T
  let q := (CommHopfAlgCat.mkQuotient H T).hom
  have hpoint : ∀ p : Q →ₐ[K] K, p = Bialgebra.counitAlgHom K Q := by
    intro p
    let gp : WithConv (Q →ₐ[K] K) := toConv p
    let g := CommHopfAlgCat.quotientPointsHom H T (CommAlgCat.of K K) gp
    have hgI : g ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of K K) := by
      apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I
        (CommAlgCat.of K K) g).mpr
      intro b hb
      exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H T
        (CommAlgCat.of K K) g).mp
        (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H T
          (CommAlgCat.of K K) gp) b (Ideal.mem_sup_left hb)
    have hgU : g ∈ CommHopfAlgCat.quotientPointsSubgroup H U (CommAlgCat.of K K) := by
      apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H U
        (CommAlgCat.of K K) g).mpr
      intro b hb
      exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H T
        (CommAlgCat.of K K) g).mp
        (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H T
          (CommAlgCat.of K K) gp) b (Ideal.mem_sup_right hb)
    have hg : g = 1 := BorelRootUnipotent.torus_point_intersection_eq_one
      I J hJ π hπ hker g hgI hgU
    have hgp : gp = 1 :=
      (CommHopfAlgCat.quotientPointsHom_injective H T (CommAlgCat.of K K))
        (by simpa only [map_one] using hg)
    exact congrArg WithConv.ofConv hgp
  have hIrange :
      (derivationCompLieHom (B := K) (CommHopfAlgCat.mkQuotient H I).hom).range =
        diagonalizableTangentImage π := by
    ext d
    change d ∈ (derivationCompLieHom (B := K) (CommHopfAlgCat.mkQuotient H I).hom).range ↔
      d ∈ (derivationCompLieHom (B := K) π).range
    rw [tangent_mem_hopfQuotient_iff,
      tangent_mem_range_iff_kills_kernel π hπ d]
    exact forall_congr' fun b => by
      change (b ∈ I.toIdeal → d b = 0) ↔ (π b = 0 → d b = 0)
      rw [hker b]
  have hzero : (derivationCompLieHom (B := K) q).range = ⊥ := by
    change (derivationCompLieHom (B := K) (CommHopfAlgCat.mkQuotient H T).hom).range = ⊥
    rw [hopfQuotient_sup_tangentImage, hIrange]
    rw [inf_comm]
    exact BorelRootUnipotentTangent.inf_torus_eq_bot J hJ π hπ
  have htan : Subsingleton
      (Derivation K Q (Bialgebra.CounitAlgebra K Q K)) := by
    have hinj : Function.Injective (derivationCompLieHom (B := K) q) :=
      derivationCompLieHom_injective_of_surjective q
        (CommHopfAlgCat.mkQuotient_surjective H T)
    constructor
    intro d e
    apply hinj
    have hd : derivationCompLieHom (B := K) q d = 0 := by
      have hm : derivationCompLieHom (B := K) q d ∈
          (derivationCompLieHom (B := K) q).range := ⟨d, rfl⟩
      rw [hzero] at hm
      simpa using hm
    have he : derivationCompLieHom (B := K) q e = 0 := by
      have hm : derivationCompLieHom (B := K) q e ∈
          (derivationCompLieHom (B := K) q).range := ⟨e, rfl⟩
      rw [hzero] at hm
      simpa using hm
    rw [hd, he]
  have haug : Bialgebra.AugmentationIdeal K Q = ⊥ :=
    FiniteType.aug_eq_bot_of_point_and_tangent_zero hpoint htan
  -- Pull the zero augmentation ideal back through the quotient.
  apply HopfIdeal.ext
  intro b
  change b ∈ T ↔ b ∈ HopfIdeal.augmentation K B
  change b ∈ T.toIdeal ↔ b ∈ HopfIdeal.augmentation K B
  rw [← CommHopfAlgCat.mkQuotient_eq_zero_iff H T b]
  have hcb : Coalgebra.counit (R := K) (q b) =
      Coalgebra.counit (R := K) b := by
    exact DFunLike.congr_fun (BialgHom.counitAlgHom_comp q) b
  rw [HopfIdeal.mem_augmentation, ← hcb]
  have hzero : q b ∈ Bialgebra.AugmentationIdeal K Q ↔ q b = 0 := by
    rw [haug]
    simp
  exact hzero.symm

/-- The torus and the Borel's Ga-only subgroup intersect in
the identity over an arbitrary commutative value algebra. -/
theorem BorelRootUnipotent.torus_intersection_eq_one
    (I J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (A : CommAlgCat.{v} K)
    (g : WithConv (B →ₐ[K] A))
    (hgT : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I A)
    (hgU : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) (borelRootUnipotentHopfIdeal J π hπ) A) :
    g = 1 := by
  let U := borelRootUnipotentHopfIdeal J π hπ
  have hsup : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) (I ⊔ U) A := by
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K B) (I ⊔ U) A g).mpr
    intro b hb
    obtain ⟨x, hx, y, hy, rfl⟩ := HopfIdeal.mem_sup.mp hb
    rw [map_add,
      (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
        (CommHopfAlgCat.of K B) I A g).mp hgT x hx,
      (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
        (CommHopfAlgCat.of K B) U A g).mp hgU y hy, add_zero]
  rw [BorelRootUnipotent.torus_sup_eq_augmentation I J hJ π hπ hker] at hsup
  exact CommHopfAlgCat.eq_one_of_mem_quotientPointsSubgroup_augmentation
    (CommHopfAlgCat.of K B) A hsup

/-- Multiplication of the two closed-subgroup point sets is
injective for every commutative `K`-algebra. -/
theorem BorelRootUnipotent.torus_product_injective
    (I J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (A : CommAlgCat.{v} K) :
    Function.Injective
      (fun p :
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I A ×
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
          (borelRootUnipotentHopfIdeal J π hπ) A =>
        (p.1.1 : WithConv (B →ₐ[K] A)) * p.2.1) := by
  intro a b hab
  change (a.1.1 : WithConv (B →ₐ[K] A)) * a.2.1 =
    b.1.1 * b.2.1 at hab
  let g : WithConv (B →ₐ[K] A) := b.1.1⁻¹ * a.1.1
  have hgU : g = b.2.1 * a.2.1⁻¹ := by
    dsimp [g]
    calc
      b.1.1⁻¹ * a.1.1 = b.1.1⁻¹ * (a.1.1 * a.2.1) * a.2.1⁻¹ := by group
      _ = b.1.1⁻¹ * (b.1.1 * b.2.1) * a.2.1⁻¹ := by rw [hab]
      _ = b.2.1 * a.2.1⁻¹ := by group
  have hgT : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I A := by
    exact mul_mem (inv_mem b.1.property) a.1.property
  have hgUmem : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) (borelRootUnipotentHopfIdeal J π hπ) A := by
    rw [hgU]
    exact mul_mem b.2.property (inv_mem a.2.property)
  have hg : g = 1 := BorelRootUnipotent.torus_intersection_eq_one
    I J hJ π hπ hker A g hgT hgUmem
  have ht : a.1.1 = b.1.1 := by
    calc
      a.1.1 = b.1.1 * g := by dsimp [g]; group
      _ = b.1.1 := by rw [hg, mul_one]
  have hu : a.2.1 = b.2.1 := by
    have h := hab
    rw [ht] at h
    exact mul_left_cancel h
  exact Prod.ext (Subtype.ext ht) (Subtype.ext hu)

end ReductiveGroups
