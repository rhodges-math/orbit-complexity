import OrbitComplexity.SchubertGeometry.Normality.RichardsonKernel
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Richardson kernels on the original intersection coordinate rings

The coordinate maps use the restricted schemes and their global
sections. Pullback of the ideal-sheaf identity supplies the sum identity
without identifying those rings with sections on the ambient open by notation.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

universe u

private theorem ker_of_pullback {X Y W Z : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (r : Z ⟶ W) (a : Z ⟶ X)
    (b : W ⟶ Y) (h : IsPullback r a b i) :
    r.ker = i.ker.comap b := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b

private theorem intersection_pullback {X Y : Scheme.{u}} {I : Type u}
    {K : Type u} [CommRing K] (f : X ⟶ Y) (g : Y ⟶ Spec (.of K))
    (V : I → Y.Opens) (s : {s : Finset I // s.Nonempty}) :
    IsPullback
      ((intersectionSchemeMap f g (fun i ↦ f ⁻¹ᵁ V i) V id
        (fun _ ↦ le_rfl)).app (.op s)).left
      (((intersectionOpens (fun i ↦ f ⁻¹ᵁ V i)).obj (.op s)).ι)
      (((intersectionOpens V).obj ((intersectionIndexMap id).op.obj (.op s))).ι) f := by
  let U : X.Opens := (intersectionOpens (fun i ↦ f ⁻¹ᵁ V i)).obj (.op s)
  let W : Y.Opens := (intersectionOpens V).obj ((intersectionIndexMap id).op.obj (.op s))
  let : IsOpenImmersion U.ι :=
    inferInstanceAs (IsOpenImmersion (X.ofRestrict U.isOpenEmbedding))
  let : IsOpenImmersion W.ι :=
    inferInstanceAs (IsOpenImmersion (Y.ofRestrict W.isOpenEmbedding))
  change IsPullback (f.resLE W U _) U.ι W.ι f
  apply IsOpenImmersion.isPullback
  · exact (Scheme.Hom.resLE_comp_ι _ _).symm
  · simp only [Scheme.Opens.opensRange_ι]
    classical
    change f ⁻¹ᵁ (⨅ i ∈ s.val.image id, V i) = ⨅ i ∈ s.val, f ⁻¹ᵁ V i
    rw [Finset.image_id]
    rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
    ext x
    change f x ∈ ((s.val.inf V : Y.Opens) : Set Y) ↔
      x ∈ ((s.val.inf (fun i ↦ f ⁻¹ᵁ V i) : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf, TopologicalSpace.Opens.coe_finset_inf]
    simp only [Finset.inf_eq_iInf, Set.iInf_eq_iInter, Set.mem_iInter]
    rfl

private theorem intersection_kernel_sum
    {X₁ X₂ X₃ Y : Scheme.{u}} {I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (f₃ : X₃ ⟶ Y)
    [IsClosedImmersion f₁] [IsClosedImmersion f₂] [IsClosedImmersion f₃]
    (g : Y ⟶ Spec (.of K)) (V : I → Y.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (s : {s : Finset I // s.Nonempty})
    (hker : f₃.ker = f₁.ker ⊔ f₂.ker) :
    RingHom.ker ((intersectionCoordinateMap f₃ g (fun i ↦ f₃ ⁻¹ᵁ V i)
      V id (fun _ ↦ le_rfl)).app s).hom.toRingHom =
      RingHom.ker ((intersectionCoordinateMap f₁ g (fun i ↦ f₁ ⁻¹ᵁ V i)
        V id (fun _ ↦ le_rfl)).app s).hom.toRingHom ⊔
      RingHom.ker ((intersectionCoordinateMap f₂ g (fun i ↦ f₂ ⁻¹ᵁ V i)
        V id (fun _ ↦ le_rfl)).app s).hom.toRingHom := by
  let W : Y.Opens := (intersectionOpens V).obj ((intersectionIndexMap id).op.obj (.op s))
  let r₁ : ((intersectionOpens (fun i ↦ f₁ ⁻¹ᵁ V i)).obj (.op s)).toScheme ⟶
      W.toScheme := ((intersectionSchemeMap f₁ g (fun i ↦ f₁ ⁻¹ᵁ V i)
        V id (fun _ ↦ le_rfl)).app (.op s)).left
  let r₂ : ((intersectionOpens (fun i ↦ f₂ ⁻¹ᵁ V i)).obj (.op s)).toScheme ⟶
      W.toScheme := ((intersectionSchemeMap f₂ g (fun i ↦ f₂ ⁻¹ᵁ V i)
        V id (fun _ ↦ le_rfl)).app (.op s)).left
  let r₃ : ((intersectionOpens (fun i ↦ f₃ ⁻¹ᵁ V i)).obj (.op s)).toScheme ⟶
      W.toScheme := ((intersectionSchemeMap f₃ g (fun i ↦ f₃ ⁻¹ᵁ V i)
        V id (fun _ ↦ le_rfl)).app (.op s)).left
  have hp₁ := intersection_pullback f₁ g V s
  have hp₂ := intersection_pullback f₂ g V s
  have hp₃ := intersection_pullback f₃ g V s
  have hk₁ : r₁.ker = f₁.ker.comap W.ι := ker_of_pullback f₁ _ _ _ hp₁
  have hk₂ : r₂.ker = f₂.ker.comap W.ι := ker_of_pullback f₂ _ _ _ hp₂
  have hk₃ : r₃.ker = f₃.ker.comap W.ι := ker_of_pullback f₃ _ _ _ hp₃
  have : IsClosedImmersion r₁ := MorphismProperty.of_isPullback hp₁.flip inferInstance
  have : IsClosedImmersion r₂ := MorphismProperty.of_isPullback hp₂.flip inferInstance
  have : IsClosedImmersion r₃ := MorphismProperty.of_isPullback hp₃.flip inferInstance
  have hW : IsAffineOpen W := intersectionOpens_affine V hV _
  have : IsAffine W.toScheme := hW
  have h : r₃.ker = r₁.ker ⊔ r₂.ker := by
    calc
      r₃.ker = f₃.ker.comap W.ι := hk₃
      _ = (f₁.ker ⊔ f₂.ker).comap W.ι := congrArg (fun J ↦ J.comap W.ι) hker
      _ = f₁.ker.comap W.ι ⊔ f₂.ker.comap W.ι :=
        Scheme.IdealSheafData.comap_sup _ _ _
      _ = r₁.ker ⊔ r₂.ker := congrArg₂ (fun I J ↦ I ⊔ J) hk₁.symm hk₂.symm
  let T : W.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have ht : r₃.ker.ideal T = r₁.ker.ideal T ⊔ r₂.ker.ideal T :=
    congrArg (fun J : W.toScheme.IdealSheafData ↦ J.ideal T) h
  change RingHom.ker r₃.appTop.hom =
    RingHom.ker r₁.appTop.hom ⊔ RingHom.ker r₂.appTop.hom
  exact (Scheme.Hom.ker_apply r₃ T).symm.trans
    (ht.trans (congrArg₂ (fun I J ↦ I ⊔ J)
      (Scheme.Hom.ker_apply r₁ T) (Scheme.Hom.ker_apply r₂ T)))

end
end SchubertGeometry

namespace SchubertGeometry

universe u

/-- The Richardson pullback on each intersection coordinate ring has
the sum of the two Schubert pullback kernels on that same ring. -/
theorem richardson_coordinate_ker {K I : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (v w : G.weylGroup)
    (U : I → (flagVariety G).scheme.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty}) :
    RingHom.ker ((@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (richardsonVariety G v w).scheme (flagVariety G).scheme I I K kField.toCommRing
        (richardsonInclusion G v w).left (flagVariety G).toSpec
      (fun i ↦ (richardsonInclusion G v w).left ⁻¹ᵁ U i) U id
        (fun _ ↦ le_rfl)).app s).hom.toRingHom =
      RingHom.ker ((@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (schubertVariety G w).scheme (flagVariety G).scheme I I K kField.toCommRing (schubertInclusion
        G w).left (flagVariety G).toSpec
        (fun i ↦ (schubertInclusion G w).left ⁻¹ᵁ U i) U id
          (fun _ ↦ le_rfl)).app s).hom.toRingHom ⊔
      RingHom.ker ((@FrobeniusSplitting.intersectionCoordinateMap.{u}
      (oppositeSchubertVariety G v).scheme (flagVariety G).scheme I I K kField.toCommRing
        (oppositeSchubertInclusion G v).left (flagVariety G).toSpec
        (fun i ↦ (oppositeSchubertInclusion G v).left ⁻¹ᵁ U i) U id
          (fun _ ↦ le_rfl)).app s).hom.toRingHom := by
  have : IsSeparated (terminal.from (flagVariety G).scheme) := by
    rw [← terminal.comp_from (flagVariety G).toSpec]
    infer_instance
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) := by
    infer_instance
  exact @SchubertGeometry.intersection_kernel_sum.{u}
    (schubertVariety G w).scheme (oppositeSchubertVariety G v).scheme
    (richardsonVariety G v w).scheme (flagVariety G).scheme I K
    kField.toCommRing inferInstance
    (schubertInclusion G w).left (oppositeSchubertInclusion G v).left
    (richardsonInclusion G v w).left inferInstance inferInstance inferInstance
    (flagVariety G).toSpec U hU s (richardson_ker_eq_sup G v w)

end SchubertGeometry
