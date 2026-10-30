import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointSubgroupCriterion
import OrbitComplexity.ReductiveGroups.Groups.Hopf.SurjectiveBialgebraDescent
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel

/-!
# Ga Unit Point Descent

A Ga morphism descends through a closed embedding when its
parameter-one point is already a point of that subgroup. -/

noncomputable section
namespace ReductiveGroups

variable {K A B : Type*} [Field K] [CharZero K]
  [CommRing A] [HopfAlgebra K A] [CommRing B] [HopfAlgebra K B]

/-- A Ga morphism whose parameter-one point comes from a closed subgroup
descends uniquely to its coordinate algebra. The descended parameter-one
point is the given subgroup point. -/
theorem GaUnitPointDescent.existsUnique_of_unitPoint_factor
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] SymmetricAlgebra K K)
    (g : WithConv (B →ₐ[K] K))
    (hpoint : gaAffineGroupPoints φ (Multiplicative.ofAdd (1 : K)) =
      TauCeti.AlgHom.mapDomain ρ g) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K,
      x.comp ρ = φ ∧
      gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) = g := by
  let I := TauCeti.HopfIdeal.kerOfSurjective ρ hρ
  have hmem : gaAffineGroupPoints φ (Multiplicative.ofAdd (1 : K)) ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup
        (CommHopfAlgCat.of K A) I (CommAlgCat.of K K) := by
    rw [hpoint]
    apply (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K A) I (CommAlgCat.of K K) _).mpr
    intro a ha
    have hz : ρ a = 0 := (TauCeti.HopfIdeal.mem_kerOfSurjective ρ hρ).mp ha
    simp [hz]
  have hkill : ∀ a ∈ I, φ a = 0 :=
    (GaMorphism.kills_hopfIdeal_iff_unitPoint_mem φ I).mpr hmem
  have hker : ∀ a : A, ρ a = 0 → φ a = 0 := by
    intro a ha
    exact hkill a ((TauCeti.HopfIdeal.mem_kerOfSurjective ρ hρ).mpr ha)
  let x := surjectiveBialgebraDescend ρ hρ φ hker
  have hcomp : x.comp ρ = φ := surjectiveBialgebraDescend_comp ρ hρ φ hker
  have hxpoint : gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) = g := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hρ b
    have h := congrArg (fun z : WithConv (A →ₐ[K] K) => z.ofConv a) hpoint
    have hc : x (ρ a) = φ a := by
      have := congrArg (fun z : A →ₐc[K] SymmetricAlgebra K K => z a) hcomp
      simpa only [BialgHom.comp_apply] using this
    simp only [gaAffineGroupPoints, MonoidHom.comp_apply,
      TauCeti.AlgHom.mapDomain_apply_apply] at h
    rw [← hc] at h
    simpa only [gaAffineGroupPoints, MonoidHom.comp_apply,
      TauCeti.AlgHom.mapDomain_apply_apply] using h
  refine ⟨x, ⟨hcomp, hxpoint⟩, ?_⟩
  intro y hy
  exact surjectiveBialgebraDescend_unique ρ hρ φ hker y hy.1

end ReductiveGroups
