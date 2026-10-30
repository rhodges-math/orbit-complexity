import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeComponentKernels
import OrbitComplexity.SchubertGeometry.Cells.OppositeAffineComponents
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeCoordinateStages

/-! # Coordinate kernels of opposite Schubert components -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite ReductiveGroups FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private quotient_component from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

open private tensor_functor tensor_comparison from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates

/-- Higher opposite Schubert kernels and the identity kernel retain their minimal-prime
relations on the coefficient charts of the chosen stage. -/
theorem opposite_component_kernels
    {K T : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀)))
    (qP : (flagVariety G).scheme ⟶ P.left) (start : CoefficientStage S₀)
    (selected : @ClosedCoordinateStage K T G.weylGroup hK hAlg hChar
      G (oppositeSchubertSupport G) U hU S₀ P qP start) :
    let C := {s : Finset T // s.Nonempty}
    let F := FrobeniusSplitting.intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U)
    let j := fun i => (flagVariety G).closedInclusion (oppositeSchubertSupport G i)
    let B := fun i => FrobeniusSplitting.intersectionCoordinates
      ((j i).left ≫ (flagVariety G).toSpec) (intersectionOpens (fun t => (j i).left ⁻¹ᵁ U t))
    let A := (Sigma.desc B).sum' F
    let _H : (Σ _ : G.weylGroup, C) ⥤ C :=
      Sigma.desc (fun _ => FrobeniusSplitting.intersectionIndexMap (id : T → T))
    let _hSk : Algebra selected.S selected.k.val :=
      (Subalgebra.inclusion selected.k.property.2).toAlgebra
    let _ : IsScalarTower selected.S selected.k.val K :=
      Subalgebra.inclusion.isScalarTower_right selected.k.property.2 K
    let S := selected.k.val
    let N := selected.N ⋙ tensor_functor selected.S selected.k.val
    let _e := fun x => tensor_comparison selected.S selected.k.val
      (selected.N.obj x) (A.obj x) (selected.e x)
    let β := Functor.whiskerRight selected.β (tensor_functor selected.S selected.k.val)
    (∀ (w : G.weylGroup) (_hw : 2 ≤ (weylCoxeterSystem G.rootBase).length w),
      ∃ a b : G.weylGroup,
        (weylCoxeterSystem G.rootBase).length a < (weylCoxeterSystem G.rootBase).length w ∧
        (weylCoxeterSystem G.rootBase).length b < (weylCoxeterSystem G.rootBase).length w ∧
        ∀ c : C,
          RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
            ((@quotient_component.{u} C inferInstance G.weylGroup S
              inferInstance (intersectionIndexMap (id : T → T)) N β w).app c).hom).toRingHom = ⊤ ∨
          RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
            ((@quotient_component.{u} C inferInstance G.weylGroup S
              inferInstance (intersectionIndexMap (id : T → T)) N β w).app c).hom).toRingHom ∈
            ((RingHom.ker ((@quotient_component.{u} C inferInstance G.weylGroup S
              inferInstance (intersectionIndexMap (id : T → T)) N β a).app c).hom.toRingHom ⊔
              RingHom.ker ((@quotient_component.{u} C inferInstance G.weylGroup S
              inferInstance (intersectionIndexMap (id : T → T)) N β b).app c).hom.toRingHom).map
                (Algebra.TensorProduct.includeRight :
                  N.obj (.inr ((intersectionIndexMap (id : T → T)).obj c)) →ₐ[S]
                    K ⊗[S] N.obj (.inr ((intersectionIndexMap (id : T → T)).obj
                      c))).toRingHom).minimalPrimes) ∧
    (∀ c : C,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C inferInstance G.weylGroup S
              inferInstance (intersectionIndexMap (id : T → T)) N β 1).app c).hom).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C inferInstance G.weylGroup S
              inferInstance (intersectionIndexMap (id : T → T)) N β 1).app c).hom).toRingHom ∈
          (⊥ : Ideal _).minimalPrimes) := by
  intro C F j B A H hSk hSkK S N e β
  have transported := @coordinate_component_kernels.{u} K T G.weylGroup
    hK hAlg hChar G (oppositeSchubertSupport G) U hU S₀ P qP start selected
  obtain ⟨hhigh, hzero⟩ := transported
  dsimp only [C, F, j, B, inferInstance, Sigma.fst, Sigma.snd] at hhigh hzero
  constructor
  · intro w hw
    have hgeometry := @exists_opposite_chart_components.{u} K hK hAlg hChar G w hw
    obtain ⟨a, b, ha, hb, hc⟩ := hgeometry
    refine ⟨a, b, ha, hb, ?_⟩
    intro c
    have hcomponent := hc T U hU c
    have hscalar := hhigh w a b c hcomponent
    exact hscalar
  · intro c
    let w1 : G.weylGroup := 1
    have hunit := @opposite_one_chart_component.{u} K T hK hAlg hChar G w1 rfl U hU c
    have hscalar := hzero w1 c hunit
    exact hscalar

end SchubertGeometry
