import OrbitComplexity.GroupActions.Actions.OrbitOpen

/-! # Openness under subgroup multiplication

A smooth multiplication of two group-valued factors transfers openness of transitive action
families to a restricted action family. The second factor acts on the source of its
morphism to the homogeneous variety.

## Main results

* `GroupActions.actionFamily_open_of_smooth_mul`: openness of restricted action families.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions
noncomputable section
universe u v

section Categorical
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (H J G X Y : C) [MonObj J] [MonObj G] [ModObj G X] [ModObj J Y]
  (i : H ⟶ G) (j : J ⟶ G) [IsMonHom j] (k : Y ⟶ X)

private def splitAction : (H ⊗ J) ⊗ Y ⟶ H ⊗ Y :=
  lift (fst (H ⊗ J) Y ≫ fst H J)
    ((fst (H ⊗ J) Y ≫ snd H J) • snd (H ⊗ J) Y)

private def splitSection : H ⊗ Y ⟶ (H ⊗ J) ⊗ Y :=
  lift (lift (fst H Y) (1 : H ⊗ Y ⟶ J)) (snd H Y)

private theorem splitSection_action :
    splitSection H J Y ≫ splitAction H J Y = 𝟙 (H ⊗ Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [splitSection, splitAction, Category.assoc, lift_fst, lift_fst_assoc,
      Category.id_comp]
  · simp only [splitSection, splitAction, Category.assoc, lift_snd, ModObj.comp_smul,
      lift_fst_assoc, one_smul, Category.id_comp]

private theorem splitAction_factor
    (hk : letI := Mod.scalarRestriction j X; IsModHom J k) :
    splitAction H J Y ≫ (i ⊗ₘ k) ≫ γ[G, X] =
      (((i ⊗ₘ j) ≫ μ[G]) ▷ Y) ≫ (G ◁ k) ≫ γ[G, X] := by
  let := Mod.scalarRestriction j X
  have : IsModHom J k := hk
  let W := (H ⊗ J) ⊗ Y
  let a : W ⟶ G := fst (H ⊗ J) Y ≫ fst H J ≫ i
  let b : W ⟶ J := fst (H ⊗ J) Y ≫ snd H J
  let y : W ⟶ Y := snd (H ⊗ J) Y
  have hr : (((i ⊗ₘ j) ≫ μ[G]) ▷ Y) ≫ (G ◁ k) =
      lift (a * (b ≫ j)) (y ≫ k) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerLeft_fst, whiskerRight_fst, lift_fst]
      change fst (H ⊗ J) Y ≫ (i ⊗ₘ j) ≫ μ[G] = lift a (b ≫ j) ≫ μ[G]
      rw [← Category.assoc]
      apply congrArg (fun t : W ⟶ G ⊗ G => t ≫ μ[G])
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [Category.assoc, tensorHom_fst, tensorHom_snd, lift_fst, lift_snd, a, b]
    · simp only [Category.assoc, whiskerLeft_snd, whiskerRight_snd_assoc, lift_snd, y]
  conv_rhs => rw [← Category.assoc, hr]
  change splitAction H J Y ≫ (i ⊗ₘ k) ≫ γ[G, X] =
    (a * (b ≫ j)) • (y ≫ k)
  rw [splitAction, lift_map_assoc]
  simp only [Category.assoc]
  change a • ((b • y) ≫ k) = (a * (b ≫ j)) • (y ≫ k)
  rw [IsModHom.map_smul]
  have hs : b • (y ≫ k) = (b ≫ j) • (y ≫ k) := by
    change lift b (y ≫ k) ≫ (j ▷ X) ≫ γ[G, X] = _
    rw [lift_whiskerRight_assoc]
    rfl
  rw [hs]
  exact (mul_smul a (b ≫ j) (y ≫ k)).symm

end Categorical

section Geometric
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (H J G X Y : Variety K) [MonObj J.toOver] [GrpObj G.toOver]
  [ModObj G.toOver X.toOver] [ModObj J.toOver Y.toOver]
  [IrreducibleSpace G.scheme]
  (i : H.toOver ⟶ G.toOver) (j : J.toOver ⟶ G.toOver) [IsMonHom j]
  (k : Y.toOver ⟶ X.toOver)

/-- A smooth product in the acting group makes the restricted action family open. -/
theorem actionFamily_open_of_smooth_mul
    (hk : letI := Mod.scalarRestriction j X.toOver; IsModHom J.toOver k)
    (hm : Smooth (((i ⊗ₘ j) ≫ μ[G.toOver]).left))
    (x : X.points) (hx : Surjective (Variety.orbitMorphism G X x).left) :
    IsOpenMap ((i ⊗ₘ k) ≫ γ[G.toOver, X.toOver]).left := by
  let m := (i ⊗ₘ j) ≫ μ[G.toOver]
  have hmY : Smooth (m ▷ Y.toOver).left := by
    change Smooth (Limits.pullback.map _ _ _ _ m.left (𝟙 Y.scheme)
      (𝟙 (Spec (CommRingCat.of K)))
      (by simpa only [Category.comp_id] using m.w.symm) (by simp))
    exact MorphismProperty.pullbackMap (P := @Smooth) hm (by infer_instance)
      m.w.symm (by simp)
  have ho : IsOpenMap ((m ▷ Y.toOver) ≫
      (G.toOver ◁ k) ≫ γ[G.toOver, X.toOver]).left :=
    (actionFamily_isOpen G X x hx Y k).comp (Scheme.Hom.isOpenMap _)
  have he := splitAction_factor H.toOver J.toOver G.toOver X.toOver Y.toOver i j k hk
  rw [← he] at ho
  let a := splitAction H.toOver J.toOver Y.toOver
  let s := splitSection H.toOver J.toOver Y.toOver
  have hs : s.left ≫ a.left = 𝟙 (H.toOver ⊗ Y.toOver).left :=
    congrArg Over.Hom.left (splitSection_action H.toOver J.toOver Y.toOver)
  have ha : Function.Surjective a.left := by
    intro z
    refine ⟨s.left z, ?_⟩
    exact congrArg (fun f : (H.toOver ⊗ Y.toOver).left ⟶
      (H.toOver ⊗ Y.toOver).left => f z) hs
  exact IsOpenMap.of_comp a.left.continuous ha ho

end Geometric
end
end GroupActions
