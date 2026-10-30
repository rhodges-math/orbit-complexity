import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusDiagonalizableOvergroup
import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Faithful Diagonal Intersection

Intersect a faithfully embedded original group with an ambient
diagonalizable subgroup, then use maximality of its torus. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K : Type u} [Field K]

/-- The intersection, expressed as an ideal in the original group,
is diagonalizable because its coordinate algebra is a quotient of the
ambient diagonalizable subgroup's coordinate algebra. -/
theorem hopfQuotient_map_groupLikeSpanned
    (A B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} K)
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (J : TauCeti.HopfIdeal K A)
    (hJ : TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient A J)) :
    TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B (J.map ρ)) := by
  let Q := J.map ρ
  let q := TauCeti.CommHopfAlgCat.mkQuotient B.obj Q
  let f := CommHopfAlgCat.ofHom (q.hom.comp ρ)
  have hf : J.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom := by
    intro a ha
    change q.hom (ρ a) = 0
    exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff B.obj Q (ρ a)).mpr
      (TauCeti.HopfIdeal.mem_map_of_mem ρ ha)
  have hfs : Function.Surjective f.hom :=
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective B.obj Q).comp hρ
  exact TauCeti.GroupLike.groupLikeSetSpan_eq_top_of_surjective
    (TauCeti.CommHopfAlgCat.liftQuotient J f hf).hom
    (TauCeti.CommHopfAlgCat.liftQuotient_surjective_of_surjective J f hf hfs) hJ

/-- An original tangent which lies in an ambient diagonalizable subgroup
containing the maximal torus already lies in that torus. -/
theorem MaximalTorus.of_faithful_diagonalizableIntersection
    [IsAlgClosed K] [CharZero K]
    (A B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} K)
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (I : TauCeti.HopfIdeal K B) (J : TauCeti.HopfIdeal K A)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K B.obj I)
    (hJI : J.map ρ ≤ I)
    (hJ : TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient A J))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : TauCeti.derivationComp (B := K) ρ d ∈
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient A.obj J).hom).range) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom).range := by
  rw [← MaximalTorus.diagonalizableOvergroup_tangentImage B I (J.map ρ)
    hI hJI (hopfQuotient_map_groupLikeSpanned A B ρ hρ J hJ)]
  rw [tangent_mem_hopfQuotient_iff]
  have hkill := (tangent_mem_hopfQuotient_iff J
    (TauCeti.derivationComp (B := K) ρ d)).mp hd
  intro b hb
  obtain ⟨a, ha, rfl⟩ := (TauCeti.HopfIdeal.mem_map_iff_of_surjective hρ).mp hb
  apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
  rw [map_zero]
  have h := congrArg (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K) (hkill a ha)
  rw [TauCeti.algEquivSelf_derivationComp_apply, map_zero] at h
  exact h

end ReductiveGroups
