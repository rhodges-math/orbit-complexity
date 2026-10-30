import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
import OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealContainmentStages
import OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeCoordinateStages
import Batteries.Tactic.Lint

/-! # Minimal primes in scalar extensions of quotient diagrams -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite FrobeniusSplitting
open scoped TensorProduct

open private tensor_functor tensor_comparison from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates

namespace SchubertGeometry

universe u

open private quotient_component from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
open private scalar_kernel from
  OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealContainmentStages

private theorem scalar_kernel_sup
    {R K A B D : Type u} [hR : CommRing R] [hK : CommRing K]
    [hA : CommRing A] [hB : CommRing B] [hD : CommRing D]
    [hRK : Algebra R K] [hRA : Algebra R A] [hRB : Algebra R B] [hRD : Algebra R D]
    (f : A →ₐ[R] B) (g : A →ₐ[R] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (RingHom.ker f.toRingHom ⊔ RingHom.ker g.toRingHom).map
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom =
        RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K f).toRingHom ⊔
          RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K g).toRingHom := by
  rw [Ideal.map_sup,
    ← @scalar_kernel.{u} R K A B hR hK hA hB hRK hRA hRB f hf,
    ← @scalar_kernel.{u} R K A D hR hK hA hD hRK hRA hRD g hg]

private theorem minimalPrime_comap_bot
    {R S : Type u} [hR : CommSemiring R] [hS : CommSemiring S]
    (e : R →+* S) (he : Function.Bijective e) (P : Ideal S)
    (h : P = ⊤ ∨ P ∈ (⊥ : Ideal S).minimalPrimes) :
    P.comap e = ⊤ ∨ P.comap e ∈ (⊥ : Ideal R).minimalPrimes := by
  have hc := @minimalPrime_comap_sup.{u,u} R S hR hS e he P ⊥ ⊥
    (by simpa only [bot_sup_eq] using h)
  simpa only [Ideal.comap_bot_of_injective e he.1, bot_sup_eq] using hc

private theorem quotient_component_minimal
    {K I C R : Type u} [hK : CommRing K] [hR : CommRing R]
    [hRK : Algebra R K] [hC : Category.{u} C]
    (H : C ⥤ C) (F : C ⥤ CommAlgCat.{u} K)
    (B : I → C ⥤ CommAlgCat.{u} K)
    (d : ∀ (i : I) (c : C), (H ⋙ F).obj c ⟶ (B i).obj c)
    (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} R)
    (e : ∀ x, K ⊗[R] N.obj x ≃ₐ[K] ((Sigma.desc B).sum' F).obj x)
    (β : Sigma.desc (fun _ : I => H) ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶
      Sum.inl_ (Σ _ : I, C) C ⋙ N)
    (hβ : ∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
        (d x.1 x.2).hom.comp (e (.inr ((Sigma.desc (fun _ : I => H)).obj x))).toAlgHom)
    (hsurj : ∀ x, Function.Surjective (β.app x).hom) :
    (∀ (w a b : I) (c : C),
      (RingHom.ker (d w c).hom.toRingHom = ⊤ ∨
        RingHom.ker (d w c).hom.toRingHom ∈
          (RingHom.ker (d a c).hom.toRingHom ⊔
            RingHom.ker (d b c).hom.toRingHom).minimalPrimes) →
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C hC I R hR H N β w).app c).hom).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C hC I R hR H N β w).app c).hom).toRingHom ∈
        ((RingHom.ker ((@quotient_component.{u} C hC I R hR H N β a).app c).hom.toRingHom ⊔
          RingHom.ker ((@quotient_component.{u} C hC I R hR H N β b).app c).hom.toRingHom).map
            (Algebra.TensorProduct.includeRight :
              N.obj (.inr (H.obj c)) →ₐ[R]
                K ⊗[R] N.obj (.inr (H.obj c))).toRingHom).minimalPrimes) ∧
    (∀ (w : I) (c : C),
      (RingHom.ker (d w c).hom.toRingHom = ⊤ ∨
        RingHom.ker (d w c).hom.toRingHom ∈ (⊥ : Ideal _).minimalPrimes) →
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C hC I R hR H N β w).app c).hom).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C hC I R hR H N β w).app c).hom).toRingHom ∈
          (⊥ : Ideal _).minimalPrimes) := by
  have hk (i : I) (c : C) :=
    @kernel_comap_of_square.{u,u,u,u}
      (K ⊗[R] N.obj (.inr (H.obj c)))
      (K ⊗[R] N.obj (.inl ⟨i, c⟩))
      (((Sigma.desc B).sum' F).obj (.inr (H.obj c)))
      (((Sigma.desc B).sum' F).obj (.inl ⟨i, c⟩))
      (@Algebra.TensorProduct.instSemiring.{u,u,u} R K (N.obj (.inr (H.obj c)))
        (@CommRing.toCommSemiring R hR)
        (@CommSemiring.toSemiring K (@CommRing.toCommSemiring K hK)) hRK
        (@CommSemiring.toSemiring (N.obj (.inr (H.obj c)))
        (@CommRing.toCommSemiring (N.obj (.inr (H.obj c)))
          (@CommAlgCat.instCommRingObjForgetAlgHomCarrier R hR (N.obj (.inr (H.obj c))))))
        (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier R hR (N.obj (.inr (H.obj c)))))
      (@Algebra.TensorProduct.instSemiring.{u,u,u} R K (N.obj (.inl ⟨i, c⟩))
        (@CommRing.toCommSemiring R hR)
        (@CommSemiring.toSemiring K (@CommRing.toCommSemiring K hK)) hRK
        (@CommSemiring.toSemiring (N.obj (.inl ⟨i, c⟩))
        (@CommRing.toCommSemiring (N.obj (.inl ⟨i, c⟩))
          (@CommAlgCat.instCommRingObjForgetAlgHomCarrier R hR (N.obj (.inl ⟨i, c⟩)))))
        (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier R hR (N.obj (.inl ⟨i, c⟩))))
      (@CommSemiring.toSemiring (((Sigma.desc B).sum' F).obj (.inr (H.obj c)))
        (@CommRing.toCommSemiring (((Sigma.desc B).sum' F).obj (.inr (H.obj c)))
        (@CommAlgCat.instCommRingObjForgetAlgHomCarrier K hK (((Sigma.desc B).sum' F).obj (.inr
          (H.obj c))))))
      (@CommSemiring.toSemiring (((Sigma.desc B).sum' F).obj (.inl ⟨i, c⟩))
        (@CommRing.toCommSemiring (((Sigma.desc B).sum' F).obj (.inl ⟨i, c⟩))
        (@CommAlgCat.instCommRingObjForgetAlgHomCarrier K hK (((Sigma.desc B).sum' F).obj (.inl ⟨i,
          c⟩)))))
      (e (.inr (H.obj c))).toRingHom (e (.inl ⟨i, c⟩)).toRingHom
      (e (.inl ⟨i, c⟩)).injective
      (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C hC I R hR H N β i).app c).hom).toRingHom
      (d i c).hom.toRingHom
      (congrArg AlgHom.toRingHom (hβ ⟨i, c⟩))
  constructor
  · intro w a b c hcomponent
    have hc := @minimalPrime_comap_sup.{u,u}
      (K ⊗[R] N.obj (.inr (H.obj c)))
      (((Sigma.desc B).sum' F).obj (.inr (H.obj c)))
      (@Algebra.TensorProduct.instCommSemiring.{u,u,u} R K (N.obj (.inr (H.obj c)))
        (@CommRing.toCommSemiring R hR)
        (@CommRing.toCommSemiring K hK) hRK
        (@CommRing.toCommSemiring (N.obj (.inr (H.obj c)))
          (@CommAlgCat.instCommRingObjForgetAlgHomCarrier R hR (N.obj (.inr (H.obj c)))))
        (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier R hR (N.obj (.inr (H.obj c)))))
      (@CommRing.toCommSemiring (((Sigma.desc B).sum' F).obj (.inr (H.obj c)))
        (@CommAlgCat.instCommRingObjForgetAlgHomCarrier K hK (((Sigma.desc B).sum' F).obj (.inr
          (H.obj c)))))
      (e (.inr (H.obj c))).toRingHom (e (.inr (H.obj c))).bijective
      (RingHom.ker (d w c).hom.toRingHom)
      (RingHom.ker (d a c).hom.toRingHom)
      (RingHom.ker (d b c).hom.toRingHom) hcomponent
    erw [← hk w c, ← hk a c, ← hk b c] at hc
    have hmap := @scalar_kernel_sup.{u} R K
      (N.obj (.inr (H.obj c))) (N.obj (.inl ⟨a, c⟩)) (N.obj (.inl ⟨b, c⟩))
      hR hK (by infer_instance) (by infer_instance) (by infer_instance)
      hRK (by infer_instance) (by infer_instance) (by infer_instance)
      ((@quotient_component.{u} C hC I R hR H N β a).app c).hom
      ((@quotient_component.{u} C hC I R hR H N β b).app c).hom
      (hsurj ⟨a, c⟩) (hsurj ⟨b, c⟩)
    erw [← hmap] at hc
    exact hc
  · intro w c hcomponent
    have hc := @minimalPrime_comap_bot.{u}
      (K ⊗[R] N.obj (.inr (H.obj c))) ((H ⋙ F).obj c)
      (@Algebra.TensorProduct.instCommSemiring.{u,u,u} R K (N.obj (.inr (H.obj c)))
        (@CommRing.toCommSemiring R hR)
        (@CommRing.toCommSemiring K hK) hRK
        (@CommRing.toCommSemiring (N.obj (.inr (H.obj c)))
          (@CommAlgCat.instCommRingObjForgetAlgHomCarrier R hR (N.obj (.inr (H.obj c)))))
        (@CommAlgCat.instAlgebraObjForgetAlgHomCarrier R hR (N.obj (.inr (H.obj c)))))
      (@CommRing.toCommSemiring ((H ⋙ F).obj c)
        (@CommAlgCat.instCommRingObjForgetAlgHomCarrier K hK ((H ⋙ F).obj c)))
      (e (.inr (H.obj c))).toRingHom (e (.inr (H.obj c))).bijective
      (RingHom.ker (d w c).hom.toRingHom) hcomponent
    erw [← hk w c] at hc
    exact hc


/-- Generic-fibre minimal-prime relations pull back to the chosen coefficient chart family. -/
theorem coordinate_component_kernels
    {K T I : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)
    (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀)))
    (qP : (flagVariety G).scheme ⟶ P.left) (start : CoefficientStage S₀)
    (selected : @ClosedCoordinateStage K T I hK hAlg hChar
      G Z U hU S₀ P qP start) :
    let C := {s : Finset T // s.Nonempty}
    let F := intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U)
    let j := fun i => (flagVariety G).closedInclusion (Z i)
    let B := fun i => intersectionCoordinates
      ((j i).left ≫ (flagVariety G).toSpec) (intersectionOpens (fun t => (j i).left ⁻¹ᵁ U t))
    let A := (Sigma.desc B).sum' F
    let H := intersectionIndexMap (id : T → T)
    let d := fun i c => (@intersectionCoordinateMap.{u}
      ((flagVariety G).closedSubvariety (Z i)).scheme
      (flagVariety G).scheme T T K hK.toCommRing (j i).left (flagVariety G).toSpec
      (fun t => (j i).left ⁻¹ᵁ U t) U id (fun _ => le_rfl)).app c
    let _hSk : Algebra selected.S selected.k.val :=
      (Subalgebra.inclusion selected.k.property.2).toAlgebra
    let _ : IsScalarTower selected.S selected.k.val K :=
      Subalgebra.inclusion.isScalarTower_right selected.k.property.2 K
    let R := selected.k.val
    let N := selected.N ⋙ tensor_functor selected.S selected.k.val
    let _e := fun x => tensor_comparison selected.S selected.k.val
      (selected.N.obj x) (A.obj x) (selected.e x)
    let β := Functor.whiskerRight selected.β (tensor_functor selected.S selected.k.val)
    (∀ (w a b : I) (c : C),
      (RingHom.ker (d w c).hom.toRingHom = ⊤ ∨
        RingHom.ker (d w c).hom.toRingHom ∈
          (RingHom.ker (d a c).hom.toRingHom ⊔
            RingHom.ker (d b c).hom.toRingHom).minimalPrimes) →
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C inferInstance I R inferInstance H N β w).app c).hom).toRingHom =
          ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C inferInstance I R inferInstance H N β w).app c).hom).toRingHom ∈
        ((RingHom.ker ((@quotient_component.{u} C inferInstance I R inferInstance H N β a).app
          c).hom.toRingHom ⊔
          RingHom.ker ((@quotient_component.{u} C inferInstance I R inferInstance H N β b).app
            c).hom.toRingHom).map
            (Algebra.TensorProduct.includeRight :
              N.obj (.inr (H.obj c)) →ₐ[R]
                K ⊗[R] N.obj (.inr (H.obj c))).toRingHom).minimalPrimes) ∧
    (∀ (w : I) (c : C),
      (RingHom.ker (d w c).hom.toRingHom = ⊤ ∨
        RingHom.ker (d w c).hom.toRingHom ∈ (⊥ : Ideal _).minimalPrimes) →
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C inferInstance I R inferInstance H N β w).app c).hom).toRingHom =
          ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K
        ((@quotient_component.{u} C inferInstance I R inferInstance H N β w).app c).hom).toRingHom ∈
          (⊥ : Ideal _).minimalPrimes) := by
  intro C F j B A H d hSk hSkK R N e β
  have properties := selected.scalarProperties
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some decl := (← Lean.getLCtx).findFromUserName? `properties |
      throwError "missing coordinate properties"
    let typ ← Lean.Meta.whnf (← Lean.instantiateMVars decl.type)
    let typ ← Lean.Core.betaReduce typ
    let goal ← goal.replaceLocalDeclDefEq decl.fvarId typ
    Lean.Elab.Tactic.replaceMainGoal [goal]
  obtain ⟨_hfp, _hn, hβ, hsurj, _hopen, _hdir⟩ := properties
  exact @quotient_component_minimal K I C R
    hK.toCommRing inferInstance inferInstance inferInstance
    H F B d N e β hβ hsurj


/-- Field specializations have prime or unit kernels and retain their minimal-prime
relations to two lower members and to the zero ideal. -/
def componentKernelStage
    {K I C : Type u} [hK : CommRing K] [hC : Category.{u} C]
    (S : Subalgebra ℤ K) (H : C ⥤ C)
    (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
    (β : Sigma.desc (fun _ : I => H) ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶
      Sum.inl_ (Σ _ : I, C) C ⋙ N)
    (rank : I → ℕ) (zero : I) (stage : CoefficientStage S) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra stage.val L],
    let _ : Algebra S L := ((algebraMap stage.val L).comp
      (Subalgebra.inclusion stage.property.2).toRingHom).toAlgebra
    (∀ x : Σ _ : I, C,
      RingHom.ker
        (Algebra.TensorProduct.lTensor (S := L) L (β.app x).hom).toRingHom = ⊤ ∨
      (RingHom.ker
        (Algebra.TensorProduct.lTensor (S := L) L (β.app x).hom).toRingHom).IsPrime) ∧
    (∀ w, 2 ≤ rank w →
      ∃ a b, rank a < rank w ∧
        rank b < rank w ∧
        ∀ c, RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (((@quotient_component.{u} C
          inferInstance I S inferInstance H N β w).app c).hom)).toRingHom = ⊤ ∨
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (((@quotient_component.{u} C
            inferInstance I S inferInstance H N β w).app c).hom)).toRingHom ∈
            (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (((@quotient_component.{u} C
              inferInstance I S inferInstance H N β a).app c).hom)).toRingHom ⊔
              RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (((@quotient_component.{u} C
                inferInstance I S inferInstance H N β b).app c).hom)).toRingHom).minimalPrimes) ∧
    (∀ c, RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (((@quotient_component.{u} C
      inferInstance I S inferInstance H N β zero).app c).hom)).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (((@quotient_component.{u} C
        inferInstance I S inferInstance H N β zero).app c).hom)).toRingHom ∈ (⊥ : Ideal
        _).minimalPrimes)

end SchubertGeometry
