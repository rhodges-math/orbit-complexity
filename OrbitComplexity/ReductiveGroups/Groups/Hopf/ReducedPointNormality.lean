import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.TensorProduct.PointSeparation

/-!
# Reduced Point Normality

Pointwise normality detects scheme-level normality when the group and
closed subgroup have reduced finite-type coordinate algebras. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv
open scoped TensorProduct

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [IsReduced B]

/-- Stability under conjugation by every `K`-point implies the
coordinate Hopf-ideal normality criterion, provided the quotient is reduced. -/
theorem isNormal_of_point_conjugation_stable
    (I : TauCeti.HopfIdeal K B) [IsReduced (B ⧸ I.toIdeal)]
    (hstable : ∀ (g : WithConv (B →ₐ[K] K)) (b : B), b ∈ I →
      affineGroupConjugationBialgHom g b ∈ I) : I.IsNormal := by
  rw [TauCeti.HopfIdeal.isNormal_iff_conjugation_mem]
  intro b hb
  let q : B →ₐ[K] B ⧸ I.toIdeal := Ideal.Quotient.mkₐ K I.toIdeal
  let t : B ⊗[K] (B ⧸ I.toIdeal) :=
    Algebra.TensorProduct.map (AlgHom.id K B) q
      (TauCeti.HopfAlgebra.conjugationAlgHom (R := K) (H := B) b)
  have ht : t = 0 := by
    apply TauCeti.tensor_eq_zero_of_forall_productMap_eq_zero
      (fun g : B →ₐ[K] K => g)
      (fun x : (B ⧸ I.toIdeal) →ₐ[K] K => x)
    · intro a ha
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
      intro g
      simpa using ha g
    · intro a ha
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
      intro x
      simpa using ha x
    · intro g x
      let n : B →ₐ[K] K := x.comp q
      have hfixed : n (affineGroupConjugationAlgHom (toConv g) b) = 0 := by
        have hz : q (affineGroupConjugationAlgHom (toConv g) b) = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem).2 (hstable (toConv g) b hb)
        exact congrArg x hz |>.trans (map_zero x)
      have hmaps :
          (Algebra.TensorProduct.productMap g x).comp
            (Algebra.TensorProduct.map (AlgHom.id K B) q) =
              Algebra.TensorProduct.productMap g n := by
        apply Algebra.TensorProduct.ext
        · rw [AlgHom.comp_assoc,
            Algebra.TensorProduct.map_comp_includeLeft,
            AlgHom.comp_id, Algebra.TensorProduct.productMap_left,
            Algebra.TensorProduct.productMap_left]
        · apply AlgHom.ext
          intro a
          simp [n]
      change Algebra.TensorProduct.productMap g x
        (Algebra.TensorProduct.map (AlgHom.id K B) q
          (TauCeti.HopfAlgebra.conjugationAlgHom (R := K) (H := B) b)) = 0
      rw [← AlgHom.comp_apply, hmaps]
      have hpoint :
          (Algebra.TensorProduct.productMap g n)
            (TauCeti.HopfAlgebra.conjugationAlgHom (R := K) (H := B) b) =
              n (affineGroupConjugationAlgHom (toConv g) b) := by
        rw [← AlgHom.comp_apply,
          TauCeti.HopfAlgebra.productMap_comp_conjugationAlgHom]
        have hp := affineGroupConjugationAlgHom_point (toConv g) (toConv n)
        have hs : (IsScalarTower.toAlgHom K K K).comp g = g := by
          ext a
          simp
        simpa [n, hs] using
          congrArg (fun z : WithConv (B →ₐ[K] K) => z b) hp.symm
      exact hpoint.trans hfixed
  have hmem :
      TauCeti.HopfAlgebra.conjugationAlgHom (R := K) (H := B) b ∈
        RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K B) q) :=
    RingHom.mem_ker.mpr ht
  rw [TauCeti.HopfIdeal.ker_tensorProduct_map_id_quotient I.toIdeal] at hmem
  exact hmem

end ReductiveGroups
