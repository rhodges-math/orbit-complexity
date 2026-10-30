import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelBaseChange

/-! # Affine restriction of Borel coefficient maps -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions Opposite
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem coefficientMap_precomp (i : G.rootBase.support) (A A' : CommAlgCat.{u} K)
    (h : A →ₐ[K] A')
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    simpleBorelCoefficientMap G i A'
        ((algSpec (.of K)).map (CommAlgCat.ofHom h).op ≫ beta) =
      h.comp (simpleBorelCoefficientMap G i A beta) := by
  unfold simpleBorelCoefficientMap
  rw [Category.assoc, Functor.FullyFaithful.preimage_comp,
    Functor.FullyFaithful.preimage_map]
  rfl

/-- Affine restriction composes the Borel coefficient map and both affine parameters. -/
theorem simpleBorelCoefficient_natural (i : G.rootBase.support) (A A' : CommAlgCat.{u} K)
    (h : A →ₐ[K] A')
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    let u := (algSpec (.of K)).map (CommAlgCat.ofHom h).op
    let f := simpleBorelCoefficientMap G i A beta
    let f' := simpleBorelCoefficientMap G i A' (u ≫ beta)
    f' = h.comp f ∧
      Units.map f'.toRingHom.toMonoidHom (simpleRootCoefficient G i) =
        Units.map h.toRingHom.toMonoidHom
          (Units.map f.toRingHom.toMonoidHom (simpleRootCoefficient G i)) ∧
      f' ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
          simpleRootParameter G) =
        h (f ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
          simpleRootParameter G)) := by
  dsimp only
  refine ⟨coefficientMap_precomp G i A A' h beta, ?_, ?_⟩
  · rw [coefficientMap_precomp G i A A' h beta]
    apply Units.ext
    rfl
  · rw [coefficientMap_precomp G i A A' h beta]
    rfl

end SchubertGeometry
end
