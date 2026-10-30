import OrbitComplexity.ReductiveGroups.Groups.Hopf.HopfAutomorphismFixedSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic

/-!
# Torus Conjugation Fixed Subgroup

The fixed subgroup for conjugation by the original torus's field points. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

variable {K B M : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [CommGroup M]

private theorem torusPoints_mul_comm
    {A : Type*} [CommRing A] [Algebra K A]
    (x y : WithConv (MonoidAlgebra K M →ₐ[K] A)) : x * y = y * x := by
  apply (TauCeti.DiagonalizableGroup.pointsMulEquiv
    (R := K) (A := A) (G := M)).injective
  simp only [map_mul]
  exact mul_comm
    (TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K) (A := A) (G := M) x)
    (TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K) (A := A) (G := M) y)

/-- The original coordinate ideal fixed under conjugation by each
`K`-point of the torus quotient. -/
def torusConjugationFixedHopfIdeal
    (π : B →ₐc[K] MonoidAlgebra K M) : HopfIdeal K B :=
  hopfAutomorphismFixedHopfIdeal (fun g : WithConv (MonoidAlgebra K M →ₐ[K] K) =>
    affineGroupConjugationBialgEquiv (TauCeti.AlgHom.mapDomain π g))

/-- Over every value algebra, fixedness is exactly commutation with the
scalar extensions of all original torus `K`-points. -/
theorem mem_torusConjugationFixed_iff
    (π : B →ₐc[K] MonoidAlgebra K M)
    {A : Type*} [CommRing A] [Algebra K A]
    (x : WithConv (B →ₐ[K] A)) :
    x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) (torusConjugationFixedHopfIdeal π)
      (CommAlgCat.of K A) ↔
    ∀ g : WithConv (MonoidAlgebra K M →ₐ[K] K),
      toConv ((IsScalarTower.toAlgHom K K A).comp
        (TauCeti.AlgHom.mapDomain π g).ofConv) * x =
        x * toConv ((IsScalarTower.toAlgHom K K A).comp
          (TauCeti.AlgHom.mapDomain π g).ofConv) := by
  rw [torusConjugationFixedHopfIdeal, mem_hopfAutomorphismFixed_iff]
  constructor
  · intro h g
    have hp := congrArg toConv (h g)
    change toConv (x.ofConv.comp (affineGroupConjugationAlgHom
      (TauCeti.AlgHom.mapDomain π g))) = toConv x.ofConv at hp
    rw [affineGroupConjugationAlgHom_point] at hp
    simpa only [ofConv_toConv] using
      (show _ from (mul_inv_eq_iff_eq_mul).mp hp)
  · intro h g
    apply WithConv.toConv_injective
    change toConv (x.ofConv.comp (affineGroupConjugationAlgHom
      (TauCeti.AlgHom.mapDomain π g))) = toConv x.ofConv
    rw [affineGroupConjugationAlgHom_point]
    have hg := h g
    calc
      _ = (x * toConv ((IsScalarTower.toAlgHom K K A).comp
            (TauCeti.AlgHom.mapDomain π g).ofConv)) *
            (toConv ((IsScalarTower.toAlgHom K K A).comp
              (TauCeti.AlgHom.mapDomain π g).ofConv))⁻¹ := by rw [hg]
      _ = x := by group

/-- The torus quotient factors through the fixed subgroup: its
universal coordinate point is fixed, not merely all of its `K`-points. -/
theorem torusConjugationFixedHopfIdeal_le_ker
    (π : B →ₐc[K] MonoidAlgebra K M) :
    (torusConjugationFixedHopfIdeal π).toIdeal ≤
      RingHom.ker π.toAlgHom.toRingHom := by
  let T := MonoidAlgebra K M
  let u : WithConv (T →ₐ[K] T) := toConv (AlgHom.id K T)
  have hfixed : ∀ g : WithConv (T →ₐ[K] K),
      π.toAlgHom.comp (affineGroupConjugationAlgHom
        (TauCeti.AlgHom.mapDomain π g)) = π.toAlgHom := by
    intro g
    let t : WithConv (T →ₐ[K] T) :=
      toConv ((IsScalarTower.toAlgHom K K T).comp g.ofConv)
    have hcomm : t * u = u * t := torusPoints_mul_comm t u
    have htu : t * u * t⁻¹ = u := by
      calc
        t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [hcomm]
        _ = u := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
    have hmap := congrArg (TauCeti.AlgHom.mapDomain π) htu
    apply WithConv.toConv_injective
    have hp := affineGroupConjugationAlgHom_point
      (TauCeti.AlgHom.mapDomain π g) (toConv π.toAlgHom)
    rw [hp]
    simp only [map_mul, map_inv, TauCeti.AlgHom.mapDomain_apply,
      t, u, AlgHom.comp_assoc] at hmap
    rw [AlgHom.id_comp] at hmap
    exact hmap
  have hpoint : toConv π.toAlgHom ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup
        (CommHopfAlgCat.of K B) (torusConjugationFixedHopfIdeal π)
        (CommAlgCat.of K T) :=
    (mem_hopfAutomorphismFixed_iff _ _).mpr hfixed
  intro b hb
  rw [RingHom.mem_ker]
  exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
    (CommHopfAlgCat.of K B) (torusConjugationFixedHopfIdeal π)
    (CommAlgCat.of K T) (toConv π.toAlgHom)).mp hpoint b hb

end ReductiveGroups
