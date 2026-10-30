import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusSemisimpleDiagonalization
import OrbitComplexity.ReductiveGroups.Groups.Solvable.SolvableGaGeneratedUnipotence
import OrbitComplexity.ReductiveGroups.Groups.Representations.FaithfulMatrixBasis

/-!
# Borel Root Unipotent Torus Intersection

The fixed torus and the Borel's Ga-only subgroup have
trivial intersection on ordinary ground-field points. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv Module

universe u
variable {K B ι : Type u} [Field K]
  [CommRing B] [HopfAlgebra K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- A semisimple matrix whose deviation from the identity is nilpotent
is the identity, including the rank-zero case. -/
theorem BorelRootUnipotentTorusIntersection.one_of_semisimple_and_sub_one_nilpotent
    (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (hs : Module.End.IsSemisimple (Matrix.toLin' A))
    (hn : IsNilpotent (A - 1)) : A = 1 := by
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv'
  have hone : (1 : Module.End K (Fin n → K)) = LinearMap.id := rfl
  have hnil : IsNilpotent (Matrix.toLin' A - 1) := by
    have hm : e (A - 1) = Matrix.toLin' A - 1 := by
      change Matrix.toLin' (A - 1) = Matrix.toLin' A - 1
      simpa only [Matrix.toLin'_one, ← hone] using
        (map_sub Matrix.toLin' A 1)
    rw [← hm]
    exact hn.map e.toRingHom
  have hsemi : Module.End.IsSemisimple (Matrix.toLin' A - 1) := by
    simpa only [map_one] using
      (Module.End.isSemisimple_sub_algebraMap_iff
        (f := Matrix.toLin' A) (μ := 1)).mpr hs
  have hz := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hsemi
  apply Matrix.toLin'.injective
  have hzero : Matrix.toLin' A = 1 := sub_eq_zero.mp hz
  simpa only [Matrix.toLin'_one, ← hone] using hzero

/-- The split torus and the Ga-only subgroup generated
from the Borel have trivial intersection on `K`-points. -/
theorem BorelRootUnipotent.torus_point_intersection_eq_one
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    (I J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (g : WithConv (B →ₐ[K] K))
    (hgT : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K K))
    (hgU : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) (borelRootUnipotentHopfIdeal J π hπ)
      (CommAlgCat.of K K)) : g = 1 := by
  let f := borelRootVectorGa J π hπ
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let : LieAlgebra.IsSolvable S := borel_tangentImage_isSolvable J hJ
  have hX : ∀ r, gaAffineGroupTangent (f r) ∈ S := by
    intro r
    rw [show f r = borelRootVectorGa J π hπ r from rfl,
      borelRootVectorGa_tangent]
    exact r.2.property.2.2
  let qU : B →ₐc[K] (B ⧸ (borelRootUnipotentHopfIdeal J π hπ).toIdeal) :=
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ)).hom
  obtain ⟨v, hv⟩ := hgU
  have hgv : AlgHom.mapDomain qU v = g := hv
  have hπker : RingHom.ker π.toAlgHom.toRingHom ≤
      RingHom.ker g.ofConv.toRingHom := by
    intro b hb
    apply RingHom.mem_ker.mpr
    have hbI : b ∈ I := (hker b).mp (RingHom.mem_ker.mp hb)
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) g).mp hgT b hbI
  let tAlg : MonoidAlgebra K M →ₐ[K] K :=
    AlgHom.liftOfSurjective π.toAlgHom hπ g.ofConv hπker
  let t : WithConv (MonoidAlgebra K M →ₐ[K] K) := toConv tAlg
  have hgt : AlgHom.mapDomain π t = g := by
    apply WithConv.ofConv_injective
    exact AlgHom.liftOfSurjective_comp π.toAlgHom hπ g.ofConv hπker
  obtain ⟨V, n, b, hρ⟩ :=
    Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  let ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B :=
    Comodule.coordinateBialgHom (H := B) b
  let A : Matrix (Fin n) (Fin n) K :=
    GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g)
  have hsemi : Module.End.IsSemisimple (Matrix.toLin' A) := by
    have hs := torusMatrixPoint_isSemisimple K M n (π.comp ρ) tAlg
    have hpt : (GeneralLinear.genericMatrix K n).map
        (tAlg.comp ((π.comp ρ) : _ →ₐ[K] _)) =
          (GeneralLinear.pointsMulEquiv n
            (AlgHom.mapDomain (π.comp ρ) t) : Matrix (Fin n) (Fin n) K) := by
      rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
      rfl
    rw [hpt] at hs
    have hcomp : AlgHom.mapDomain (π.comp ρ) t = AlgHom.mapDomain ρ g := by
      rw [← hgt, AlgHom.mapDomain_comp]
      rfl
    simpa only [A, hcomp] using hs
  have hnil : IsNilpotent (A - 1) := by
    have hvnil := SolvableGaGeneratedQuotient.matrix_uniform_unipotent
      f S hX n ρ v
    have hcomp : AlgHom.mapDomain (qU.comp ρ) v = AlgHom.mapDomain ρ g := by
      rw [← hgv, AlgHom.mapDomain_comp]
      rfl
    refine ⟨n, ?_⟩
    change ((GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain (qU.comp ρ) v) : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0
      at hvnil
    rw [hcomp] at hvnil
    exact hvnil
  have hA : A = 1 :=
    BorelRootUnipotentTorusIntersection.one_of_semisimple_and_sub_one_nilpotent n A hsemi hnil
  have hpt : AlgHom.mapDomain ρ g = 1 := by
    apply (GeneralLinear.pointsMulEquiv n).injective
    apply Units.ext
    change A = ((GeneralLinear.pointsMulEquiv n)
      (1 : WithConv (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K)) :
        Matrix (Fin n) (Fin n) K)
    rw [map_one]
    exact hA
  have hinj : Function.Injective
      (AlgHom.mapDomain (A := K) ρ :
        WithConv (B →ₐ[K] K) →* WithConv
          (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K)) := by
    intro x y hxy
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    obtain ⟨z, rfl⟩ := hρ a
    have hz := congrArg
      (fun x : WithConv (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) =>
        x.ofConv z) hxy
    simpa only [AlgHom.mapDomain_apply_apply] using hz
  apply hinj
  rw [map_one]
  exact hpt

end ReductiveGroups
