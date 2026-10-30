import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-!
# Torus automorphisms from normalizer points

A rational point normalizing the maximal torus fixes its defining Hopf ideal,
since the reduced torus quotient is determined by its algebraically closed points.
Conjugation therefore descends to an automorphism of the torus coordinate Hopf algebra.

## Main definitions

* `ReductiveGroups.ReductiveGroupData.torusConjugation`: the descended Hopf automorphism.

## Main results

* `ReductiveGroups.ReductiveGroupData.torusIdeal_conjugate_eq`: invariance of the torus ideal.
* `ReductiveGroups.ReductiveGroupData.torusConjugation_points`: ambient point conjugation.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData
open TauCeti CategoryTheory

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (G : ReductiveGroupData K)

private theorem torusIdeal_conjugate_le (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    G.torusIdeal.conjugate g ≤ G.torusIdeal := by
  let : IsReduced (CommHopfAlgCat.quotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal) := G.torusAlgebra_isReduced
  apply HopfIdeal.le_of_quotientPointsSubgroup_le
    (H := CommHopfAlgCat.of K G.coordinateAlgebra) (K := K)
  intro t ht
  have hconj : g⁻¹ * t * g ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp hg t).mp ht
  have h := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff
    G.torusIdeal g (CommAlgCat.of K K) (g⁻¹ * t * g)).mpr hconj
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
    AlgHom.mapValue_id, MonoidHom.id_apply, mul_assoc, mul_inv_cancel_left,
    mul_inv_cancel, mul_one] using h

/-- A rational normalizer point fixes the defining Hopf ideal of the maximal torus. -/
theorem torusIdeal_conjugate_eq (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    G.torusIdeal.conjugate g = G.torusIdeal := by
  apply le_antisymm (G.torusIdeal_conjugate_le g hg)
  have h := HopfIdeal.conjugate_mono g (G.torusIdeal_conjugate_le g⁻¹
    (Subgroup.inv_mem _ hg))
  simpa using h


private def torusConjugationMap (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    G.torusAlgebra →ₐc[K] G.torusAlgebra :=
  Bialgebra.Quotient.liftBialgHom G.torusIdeal.toIdeal
    ((Bialgebra.Quotient.mkBialgHom G.torusIdeal.toIdeal).comp
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom) (by
        intro a ha
        change Ideal.Quotient.mk G.torusIdeal.toIdeal
          (HopfAlgebra.pointConjugationAlgHom g a) = 0
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        apply HopfIdeal.mem_conjugate.mp
        rwa [G.torusIdeal_conjugate_eq g hg])

private theorem torusConjugationMap_mk (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points))
    (a : G.coordinateAlgebra) :
    G.torusConjugationMap g hg (Ideal.Quotient.mk G.torusIdeal.toIdeal a) =
      Ideal.Quotient.mk G.torusIdeal.toIdeal (HopfAlgebra.pointConjugationAlgHom g a) := by
  rfl

private theorem torusConjugationMap_inv (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) (a : G.torusAlgebra) :
    G.torusConjugationMap g⁻¹ (Subgroup.inv_mem _ hg) (G.torusConjugationMap g hg a) = a := by
  refine Quotient.inductionOn' a ?_
  intro a
  change G.torusConjugationMap g⁻¹ (Subgroup.inv_mem _ hg)
    (G.torusConjugationMap g hg (Ideal.Quotient.mk G.torusIdeal.toIdeal a)) =
      (Ideal.Quotient.mk G.torusIdeal.toIdeal a : G.torusAlgebra)
  have h1 : G.torusConjugationMap g⁻¹ (Subgroup.inv_mem _ hg)
      (G.torusConjugationMap g hg (Ideal.Quotient.mk G.torusIdeal.toIdeal a)) =
      G.torusConjugationMap g⁻¹ (Subgroup.inv_mem _ hg)
        (Ideal.Quotient.mk G.torusIdeal.toIdeal (HopfAlgebra.pointConjugationAlgHom g a)) :=
    congrArg (G.torusConjugationMap g⁻¹ (Subgroup.inv_mem _ hg))
      (G.torusConjugationMap_mk g hg a)
  have h2 : G.torusConjugationMap g⁻¹ (Subgroup.inv_mem _ hg)
      (Ideal.Quotient.mk G.torusIdeal.toIdeal (HopfAlgebra.pointConjugationAlgHom g a)) =
      (Ideal.Quotient.mk G.torusIdeal.toIdeal
        (HopfAlgebra.pointConjugationAlgHom g⁻¹ (HopfAlgebra.pointConjugationAlgHom g a)) :
          G.torusAlgebra) := G.torusConjugationMap_mk g⁻¹ (Subgroup.inv_mem _ hg) _
  have h3 : (Ideal.Quotient.mk G.torusIdeal.toIdeal
      (HopfAlgebra.pointConjugationAlgHom g⁻¹ (HopfAlgebra.pointConjugationAlgHom g a)) :
        G.torusAlgebra) = (Ideal.Quotient.mk G.torusIdeal.toIdeal a : G.torusAlgebra) := by
    apply congrArg (fun z : G.coordinateAlgebra =>
      (Ideal.Quotient.mk G.torusIdeal.toIdeal z : G.torusAlgebra))
    have h := AlgHom.congr_fun (HopfAlgebra.pointConjugationAlgHom_mul g g⁻¹) a
    simpa only [mul_inv_cancel, HopfAlgebra.pointConjugationAlgHom_one,
      AlgHom.id_apply, AlgHom.comp_apply] using h.symm
  exact h1.trans (h2.trans h3)

/-- A normalizer point acts by a Hopf-algebra automorphism on the chosen torus. -/
def torusConjugation (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    G.torusAlgebra ≃ₐc[K] G.torusAlgebra :=
  BialgEquiv.ofBijective (G.torusConjugationMap g hg)
    (Function.bijective_iff_has_inverse.mpr ⟨G.torusConjugationMap g⁻¹
      (Subgroup.inv_mem _ hg), G.torusConjugationMap_inv g hg, by
        intro a
        simpa only [inv_inv] using G.torusConjugationMap_inv g⁻¹
          (Subgroup.inv_mem _ hg) a⟩)

/-- Torus conjugation on coordinates is induced from conjugation in the ambient group. -/
theorem torusConjugation_mk (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points))
    (a : G.coordinateAlgebra) :
    G.torusConjugation g hg (Ideal.Quotient.mk G.torusIdeal.toIdeal a) =
      Ideal.Quotient.mk G.torusIdeal.toIdeal (HopfAlgebra.pointConjugationAlgHom g a) := by
  exact G.torusConjugationMap_mk g hg a

/-- Pulling a torus point back by the coordinate automorphism gives ambient conjugation. -/
theorem torusConjugation_points (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points))
    (t : WithConv (G.torusAlgebra →ₐ[K] K)) :
    WithConv.toConv ((t.ofConv.comp (G.torusConjugation g hg).toAlgEquiv.toAlgHom).comp
      (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)) =
      g * WithConv.toConv (t.ofConv.comp (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)) * g⁻¹ := by
  unfold torusAlgebra at *
  calc
    _ = WithConv.toConv ((t.ofConv.comp (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)).comp
        (HopfAlgebra.pointConjugationAlgHom g)) := by
      apply WithConv.toConv_injective
      ext a
      simp only [AlgHom.comp_apply]
      exact congrArg t.ofConv (G.torusConjugation_mk g hg a)
    _ = _ := by
      simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
        AlgHom.mapValue_id, MonoidHom.id_apply] using
        HopfAlgebra.comp_pointConjugationAlgHom g
          (WithConv.toConv (t.ofConv.comp (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)))

end ReductiveGroups.ReductiveGroupData
