import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentTorusNormalization
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootGeneration
import OrbitComplexity.ReductiveGroups.Groups.Solvable.ConnectedGeneratedPointClosure
import OrbitComplexity.ReductiveGroups.Groups.Hopf.ReducedPointNormality
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing

/-!
# Borel Root Unipotent Normality

Normality of the Ga-only generated subgroup inside the fixed Borel. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv CategoryTheory
open scoped TensorProduct

universe u
variable {K B ι : Type u} [Field K]
  [CommRing B] [HopfAlgebra K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- For a fixed second point, universal conjugation is a regular function
of the first point. -/
theorem conjugation_evaluation_regular
    (p h : WithConv (B →ₐ[K] K)) (b : B) :
    p.ofConv ((Algebra.TensorProduct.productMap (AlgHom.id K B)
      ((IsScalarTower.toAlgHom K K B).comp h.ofConv))
      (HopfAlgebra.conjugationAlgHom (R := K) (H := B) b)) =
      h.ofConv (affineGroupConjugationAlgHom p b) := by
  let F : B ⊗[K] B →ₐ[K] K := p.ofConv.comp
    (Algebra.TensorProduct.productMap (AlgHom.id K B)
      ((IsScalarTower.toAlgHom K K B).comp h.ofConv))
  have hF : F = Algebra.TensorProduct.productMap p.ofConv h.ofConv := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [F]
    · ext a
      simp [F]
  let G : B ⊗[K] B →ₐ[K] K := h.ofConv.comp
    (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom K K B).comp p.ofConv) (AlgHom.id K B))
  have hG : G = Algebra.TensorProduct.productMap p.ofConv h.ofConv := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [G]
    · ext a
      simp [G]
  change F (HopfAlgebra.conjugationAlgHom (R := K) (H := B) b) =
    G (HopfAlgebra.conjugationAlgHom (R := K) (H := B) b)
  rw [hF, hG]

/-- A subgroup normalized by an ordinary point group is also normalized
by every rational point of that point group's Hopf-ideal closure. -/
theorem BorelRootUnipotentNormality.conjugation_stable_of_vanishing_closure
    (S T : Subgroup (WithConv (B →ₐ[K] K)))
    (J U : HopfIdeal K B)
    (hJ : J = HopfIdeal.vanishingIdeal S)
    (hU : U = HopfIdeal.vanishingIdeal T)
    (hnorm : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T)
    (p : WithConv (B →ₐ[K] K))
    (hp : p ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) J (CommAlgCat.of K K))
    (b : B) (hb : b ∈ U) :
    affineGroupConjugationBialgHom p b ∈ U := by
  rw [hU, HopfIdeal.mem_vanishingIdeal]
  intro t
  let F : B ⊗[K] B →ₐ[K] B := Algebra.TensorProduct.productMap
    (AlgHom.id K B) ((IsScalarTower.toAlgHom K K B).comp t.val.ofConv)
  have hF : F (HopfAlgebra.conjugationAlgHom (R := K) (H := B) b) ∈ J := by
    rw [hJ, HopfIdeal.mem_vanishingIdeal]
    intro s
    have hst : s.val * t.val * s.val⁻¹ ∈ T := hnorm s.val s.property t.val t.property
    have hz := (HopfIdeal.mem_vanishingIdeal T b).mp (hU ▸ hb) ⟨_, hst⟩
    have hs := affineGroupConjugationAlgHom_point s.val t.val
    have hval := congrArg (fun z : WithConv (B →ₐ[K] K) => z.ofConv b) hs
    have hzero : t.val.ofConv (affineGroupConjugationAlgHom s.val b) = 0 :=
      hval.trans hz
    exact (conjugation_evaluation_regular s.val t.val b).trans hzero
  have hpzero := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
    (CommHopfAlgCat.of K B) J (CommAlgCat.of K K) p).mp hp _ hF
  exact (conjugation_evaluation_regular p t.val b).symm.trans hpzero

private def borelRootClosedPointSubgroup
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) : Subgroup (WithConv (B →ₐ[K] K)) :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)

/-- Every point of the split torus normalizes the
closed Ga-generated subgroup on ordinary points. -/
theorem BorelRootClosedPointSubgroup.torus_normalizer
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π)
    (g : WithConv (MonoidAlgebra K M →ₐ[K] K)) :
    AlgHom.mapDomain π g ∈ Subgroup.normalizer (borelRootClosedPointSubgroup J π hπ) := by
  let U := borelRootUnipotentHopfIdeal J π hπ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hconj (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
      (z : WithConv (B →ₐ[K] K))
      (hz : z ∈ borelRootClosedPointSubgroup J π hπ) :
      AlgHom.mapDomain π t * z * (AlgHom.mapDomain π t)⁻¹ ∈
        borelRootClosedPointSubgroup J π hπ := by
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K B) U (CommAlgCat.of K K) _).mpr
    intro b hb
    have hpoint := affineGroupConjugationAlgHom_point
      (AlgHom.mapDomain π t) z
    have hzero := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K B) U (CommAlgCat.of K K) z).mp hz _
      (BorelRootUnipotentHopfIdeal.torus_point_conjugation J π hπ t b hb)
    have hval := congrArg (fun y : WithConv (B →ₐ[K] K) => y.ofConv b) hpoint
    exact hval.symm.trans hzero
  constructor
  · intro hx
    exact hconj g x hx
  · intro hx
    have hback := hconj g⁻¹
      (AlgHom.mapDomain π g * x * (AlgHom.mapDomain π g)⁻¹) hx
    have hmap : AlgHom.mapDomain π g⁻¹ = (AlgHom.mapDomain π g)⁻¹ :=
      map_inv (AlgHom.mapDomain π) g
    rw [hmap] at hback
    simpa [mul_assoc] using hback

/-- The ordinary point subgroup generated by the torus and all
Borel character Ga maps normalizes the closed Ga-only subgroup. -/
theorem BorelRootMixedGeneratedPointSubgroup.normalizes
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :
    connectedGeneratedPointSubgroup (CommHopfAlgCat.of K B)
      (borelRootGeneratorCodomain J π) (borelRootGeneratorFamily J π hπ) ≤
      Subgroup.normalizer (borelRootClosedPointSubgroup J π hπ) := by
  let _ := fun j => borelRootGeneratorCodomain_finiteType J π hπ j
  let _ := fun j => borelRootGeneratorCodomain_isDomain J π j
  let _ : ∀ j, IsReduced (borelRootGeneratorCodomain J π j) :=
    fun j => inferInstance
  rw [connectedGeneratedPointSubgroup, Subgroup.closure_le]
  intro x hx
  obtain ⟨j, p, rfl⟩ := Set.mem_iUnion.mp hx
  cases j with
  | none =>
      change AlgHom.mapDomain π p ∈ _
      exact BorelRootClosedPointSubgroup.torus_normalizer J π hπ p
  | some r =>
      apply (borelRootClosedPointSubgroup J π hπ).le_normalizer
      apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
        (CommHopfAlgCat.of K B) (borelRootUnipotentHopfIdeal J π hπ)
        (CommAlgCat.of K K) _).mpr
      intro b hb
      change p.ofConv (borelRootVectorGa J π hπ r b) = 0
      have hzero : borelRootVectorGa J π hπ r b = 0 :=
        (gaMorphism_kills_hopfIdeal_iff (borelRootVectorGa J π hπ r)
          (borelRootUnipotentHopfIdeal J π hπ)).mpr
            (fun a ha => gaGenerated_tangent_eq_zero_on_ideal
              (borelRootVectorGa J π hπ) r a ha) b hb
      change (p.ofConv : SymmetricAlgebra K K →ₐ[K] K)
        (borelRootVectorGa J π hπ r b) = 0
      exact (congrArg p.ofConv hzero).trans (map_zero p.ofConv)

/-- Every point of the Borel preserves the Ga-only ideal.
The mixed-generator equality supplies Zariski density, while the preceding
regularity lemma carries normalization to all Borel points. -/
theorem BorelRootUnipotentHopfIdeal.borel_point_conjugation
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι]
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (p : WithConv (B →ₐ[K] K))
    (hp : p ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) J (CommAlgCat.of K K))
    (b : B) (hb : b ∈ borelRootUnipotentHopfIdeal J π hπ) :
    affineGroupConjugationBialgHom p b ∈
      borelRootUnipotentHopfIdeal J π hπ := by
  let f := borelRootVectorGa J π hπ
  let S := connectedGeneratedPointSubgroup (CommHopfAlgCat.of K B)
    (borelRootGeneratorCodomain J π) (borelRootGeneratorFamily J π hπ)
  let T := borelRootClosedPointSubgroup J π hπ
  have hJT : J = HopfIdeal.vanishingIdeal S := by
    let _ := fun j => borelRootGeneratorCodomain_finiteType J π hπ j
    let _ := fun j => borelRootGeneratorCodomain_isDomain J π j
    let _ : ∀ j, IsReduced (borelRootGeneratorCodomain J π j) :=
      fun j => inferInstance
    rw [← borel_commonKernelRootGenerators_eq I J hJI hI hJ π hπ hker hB,
      CommonKernelHopfIdeal.eq_generated_vanishingIdeal]
  have hUT : borelRootUnipotentHopfIdeal J π hπ =
      HopfIdeal.vanishingIdeal T := by
    let U := borelRootUnipotentHopfIdeal J π hπ
    have hTU : gaGeneratedPointSubgroup f ≤ T := by
      apply (HopfIdeal.le_vanishingIdeal_iff (gaGeneratedPointSubgroup f) U).mp
      exact (gaGeneratedHopfIdeal_eq_vanishingIdeal f).le
    apply le_antisymm
    · exact (HopfIdeal.le_vanishingIdeal_iff T U).mpr le_rfl
    · intro a ha
      change a ∈ U
      rw [show U = HopfIdeal.vanishingIdeal (gaGeneratedPointSubgroup f) from
        gaGeneratedHopfIdeal_eq_vanishingIdeal f]
      apply (HopfIdeal.mem_vanishingIdeal (gaGeneratedPointSubgroup f) a).mpr
      intro t
      exact (HopfIdeal.mem_vanishingIdeal T a).mp ha ⟨t.val, hTU t.property⟩
  have hnorm : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
    intro s hs t ht
    exact ((Subgroup.mem_normalizer_iff.mp
      (BorelRootMixedGeneratedPointSubgroup.normalizes J π hπ hs)) t).mp ht
  exact BorelRootUnipotentNormality.conjugation_stable_of_vanishing_closure S T J
    (borelRootUnipotentHopfIdeal J π hπ) hJT hUT hnorm p hp b hb

/-- Mapping the Ga-only ideal into the Borel quotient retains
reducedness of its coordinate quotient. -/
theorem borelRootUnipotentMap_quotient_isReduced
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :
    let q := (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom
    IsReduced ((B ⧸ J.toIdeal) ⧸
      ((borelRootUnipotentHopfIdeal J π hπ).map q).toIdeal) := by
  intro q
  let U := borelRootUnipotentHopfIdeal J π hπ
  have hJU : J ≤ U := borel_le_borelRootUnipotentHopfIdeal J π hπ
  have hq : Function.Surjective q :=
    CommHopfAlgCat.mkQuotient_surjective (CommHopfAlgCat.of K B) J
  have hrad : U.toIdeal.IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced]
    change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B) U)
    unfold U borelRootUnipotentHopfIdeal
    infer_instance
  have hker : RingHom.ker (q : B →+* (B ⧸ J.toIdeal)) ≤ U.toIdeal := by
    intro b hb
    apply hJU
    exact (CommHopfAlgCat.mkQuotient_eq_zero_iff
      (CommHopfAlgCat.of K B) J b).mp hb
  have hmaprad : (Ideal.map (q : B →+* (B ⧸ J.toIdeal)) U.toIdeal).IsRadical := by
    have hm := Ideal.map_radical_of_surjective hq hker (I := U.toIdeal)
    rw [hrad.radical] at hm
    exact (Ideal.radical_eq_iff).mp hm.symm
  rw [← Ideal.isRadical_iff_quotient_reduced]
  change (Ideal.map (q : B →+* (B ⧸ J.toIdeal)) U.toIdeal).IsRadical
  exact hmaprad

/-- The fixed-point coordinate conjugation commutes with a
surjective coordinate morphism, with the point pulled back contravariantly. -/
theorem affineGroupConjugationBialgHom_natural
    {Q : Type u} [CommRing Q] [HopfAlgebra K Q]
    (q : B →ₐc[K] Q) (g : WithConv (Q →ₐ[K] K)) (b : B) :
    q (affineGroupConjugationBialgHom (AlgHom.mapDomain q g) b) =
      affineGroupConjugationBialgHom g (q b) := by
  change (q.toAlgHom.comp (affineGroupConjugationAlgHom
    (AlgHom.mapDomain q g))) b =
      ((affineGroupConjugationAlgHom g).comp q.toAlgHom) b
  apply congrArg (fun f : B →ₐ[K] Q => f b)
  apply WithConv.toConv_injective
  have hleft := affineGroupConjugationAlgHom_point
    (AlgHom.mapDomain q g) (toConv q.toAlgHom)
  have hright := affineGroupConjugationAlgHom_point g
    (toConv (AlgHom.id K Q))
  change toConv (q.toAlgHom.comp (affineGroupConjugationAlgHom
    (AlgHom.mapDomain q g))) = _ at hleft
  change toConv (affineGroupConjugationAlgHom g) = _ at hright
  change toConv (q.toAlgHom.comp (affineGroupConjugationAlgHom
    (AlgHom.mapDomain q g))) =
      toConv ((affineGroupConjugationAlgHom g).comp q.toAlgHom)
  rw [hleft]
  have hm := congrArg (AlgHom.mapDomain q) hright
  change toConv ((affineGroupConjugationAlgHom g).comp q.toAlgHom) = _ at hm
  simp only [map_mul, map_inv] at hm
  rw [hm]
  rfl

/-- The Ga-only Borel-root subgroup is normal inside the
original Borel quotient. This is the Hopf-ideal normality predicate in
`B/J`, rather than a statement only about selected generators. -/
theorem borelRootUnipotentMap_isNormal_inBorel
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι]
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    ((borelRootUnipotentHopfIdeal J π hπ).map
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).IsNormal := by
  let Q := B ⧸ J.toIdeal
  let q : B →ₐc[K] Q :=
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom
  let U := borelRootUnipotentHopfIdeal J π hπ
  have hq : Function.Surjective q :=
    CommHopfAlgCat.mkQuotient_surjective (CommHopfAlgCat.of K B) J
  let _ : Algebra.FiniteType K Q := inferInstance
  let _ : IsReduced Q := borelQuotient_isReduced J hJ
  let _ : IsReduced (Q ⧸ (U.map q).toIdeal) :=
    borelRootUnipotentMap_quotient_isReduced J π hπ
  apply isNormal_of_point_conjugation_stable (K := K) (B := Q) (U.map q)
  intro g y hy
  obtain ⟨b, hb, rfl⟩ := (HopfIdeal.mem_map_iff_of_surjective hq).mp hy
  let p : WithConv (B →ₐ[K] K) := AlgHom.mapDomain q g
  have hp : p ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) J (CommAlgCat.of K K) :=
    CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
      (CommHopfAlgCat.of K B) J (CommAlgCat.of K K) g
  have hb' := BorelRootUnipotentHopfIdeal.borel_point_conjugation
    I J hJI hI hJ π hπ hker hB p hp b hb
  rw [← affineGroupConjugationBialgHom_natural q g b]
  exact HopfIdeal.mem_map_of_mem q hb'

end ReductiveGroups
