import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialInjective
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import TauCeti.Algebra.Bialgebra.GroupLike.Map
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Torus Tangent Containment

In characteristic zero, containment of the tangent of a split
torus implies containment of that torus in a closed subgroup. The proof
uses character separation and linear independence of group-like elements;
the intersection subgroup need not be assumed connected. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K ι : Type*} [Field K] [CharZero K]

/-- A Hopf map out of a split torus coordinate algebra is injective if every
torus tangent vanishes on its kernel. -/
theorem TorusCoordinateMap.injective_of_tangents_kill_kernel
    {A : Type*} [CommRing A] [HopfAlgebra K A]
    (q : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐc[K] A)
    (hq : ∀ d : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      ∀ a, q a = 0 → d a = 0) : Function.Injective q := by
  let v : Multiplicative (ι →₀ ℤ) → _root_.GroupLike K A := fun α =>
    ⟨q (MonoidAlgebra.single α 1),
      (MonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) α).map q⟩
  have hv : Function.Injective v := by
    intro α β h
    apply characterDifferential_injective (K := K)
    apply LinearMap.ext
    intro d
    have heq : q (MonoidAlgebra.single α 1) = q (MonoidAlgebra.single β 1) :=
      congrArg _root_.GroupLike.val h
    have hz := hq d (MonoidAlgebra.single α 1 - MonoidAlgebra.single β 1)
      (by rw [map_sub, heq, sub_self])
    rw [map_sub, sub_eq_zero] at hz
    exact congrArg (Bialgebra.CounitAlgebra.algEquivSelf K
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K) hz
  have hlin : LinearIndependent K (fun α => q (MonoidAlgebra.single α 1)) :=
    linearIndep_groupLikeVal.comp v hv
  have hc := (MonoidAlgebra.basis (Multiplicative (ι →₀ ℤ)) K).injective_constr_of_linearIndependent
    (R₂ := K) hlin
  have heq : (MonoidAlgebra.basis (Multiplicative (ι →₀ ℤ)) K).constr K
      (fun α => q (MonoidAlgebra.single α 1)) = q.toLinearMap := by
    apply (MonoidAlgebra.basis (Multiplicative (ι →₀ ℤ)) K).ext
    intro α
    rw [Module.Basis.constr_basis]
    rfl
  rw [heq] at hc
  intro a b hab
  apply hc
  exact hab

set_option maxHeartbeats 400000 in
/-- A closed subgroup of a split torus with the whole torus tangent is the
torus itself.  -/
theorem torusHopfIdeal_eq_bot_of_tangents_kill
    (J : HopfIdeal K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))))
    (hJ : ∀ d : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      ∀ a ∈ J, d a = 0) : J = ⊥ := by
  let C := _root_.CommHopfAlgCat.of K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
  let q := (CommHopfAlgCat.mkQuotient C J).hom
  have hq : Function.Injective q :=
    TorusCoordinateMap.injective_of_tangents_kill_kernel q (by
      intro d a ha
      exact hJ d a ((CommHopfAlgCat.mkQuotient_eq_zero_iff C J a).mp ha))
  apply bot_unique
  intro a ha
  have hz : q a = 0 := (CommHopfAlgCat.mkQuotient_eq_zero_iff C J a).mpr ha
  have ha0 : a = 0 := hq (hz.trans (map_zero q).symm)
  simpa only [ha0] using (show (0 : MonoidAlgebra K
    (Multiplicative (ι →₀ ℤ))) ∈ (⊥ : HopfIdeal K _) from zero_mem _)

/-- If the split-torus differential lies in a closed subgroup's
tangent, its coordinate map annihilates that subgroup's defining ideal. -/
theorem TorusCoordinateMap.kills_of_tangent_containment
    {B : Type*} [CommRing B] [HopfAlgebra K B]
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (J : HopfIdeal K B)
    (hJ : (derivationCompLieHom (B := K) π).range ≤
      (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of K B) J).hom).range) :
    ∀ a ∈ J, π a = 0 := by
  have heq : J.map π = ⊥ := torusHopfIdeal_eq_bot_of_tangents_kill (J.map π) (by
    intro d a ha
    obtain ⟨b, hb, rfl⟩ := (HopfIdeal.mem_map_iff_of_surjective hπ).mp ha
    have hd := hJ (LieHom.mem_range_self (derivationCompLieHom (B := K) π) d)
    have hz := (tangent_mem_hopfQuotient_iff J _).mp hd b hb
    apply (Bialgebra.CounitAlgebra.algEquivSelf K
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K).injective
    have he := congrArg (Bialgebra.CounitAlgebra.algEquivSelf K B K) hz
    rw [derivationCompLieHom_apply, algEquivSelf_derivationComp_apply, map_zero] at he
    exact he)
  intro a ha
  have hmem := HopfIdeal.mem_map_of_mem π ha
  rw [heq] at hmem
  exact hmem

end ReductiveGroups
