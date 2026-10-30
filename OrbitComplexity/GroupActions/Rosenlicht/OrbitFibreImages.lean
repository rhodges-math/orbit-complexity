import OrbitComplexity.GroupActions.Rosenlicht.RelationFibreMaps
import OrbitComplexity.GroupActions.Actions.Orbits

/-!
# Orbit images in relation fibres

Each orbit lies in the closed image of its relation fibre. Points of that fibre
coming from the relation morphism lie in the orbit morphism's image. Product
fibres over rational points identify the relevant group parameter.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

private def orbitSection (x : X.points) : H.toOver ⟶ (productVariety H X).toOver :=
  lift (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x)

omit [GrpObj H.toOver] [ModObj H.toOver X.toOver] in
private lemma orbitSection_fst (x : X.points) (h : H.scheme) :
    (fst H.toOver X.toOver).left ((orbitSection H X x).left h) = h := by
  exact congrArg (fun f : H.toOver ⟶ H.toOver ↦ f.left h)
    (lift_fst (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x))

omit [GrpObj H.toOver] [ModObj H.toOver X.toOver] in
private lemma orbitSection_snd (x : X.points) (h : H.scheme) :
    (snd H.toOver X.toOver).left ((orbitSection H X x).left h) = X.pointMap x := by
  have hs := congrArg (fun f : H.toOver ⟶ X.toOver ↦ f.left h)
    (lift_snd (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x))
  apply hs.trans
  change x.val ((toUnit H.toOver).left h) = x.val (IsLocalRing.closedPoint K)
  exact congrArg x.val (Subsingleton.elim _ _)

omit [GrpObj H.toOver] [ModObj H.toOver X.toOver] in
private lemma eq_orbitSection (x : X.points) (t : (productVariety H X).scheme)
    (ht : (snd H.toOver X.toOver).left t = X.pointMap x) :
    (orbitSection H X x).left ((fst H.toOver X.toOver).left t) = t := by
  let f := (snd H.toOver X.toOver).left
  let j : f.fiber (X.pointMap x) := (f.fiberHomeo (X.pointMap x)).symm ⟨t, ht⟩
  let k : f.fiber (X.pointMap x) := (f.fiberHomeo (X.pointMap x)).symm
    ⟨(orbitSection H X x).left ((fst H.toOver X.toOver).left t), orbitSection_snd H X x _⟩
  have he : productSecondFibreHomeomorph H X x k = productSecondFibreHomeomorph H X x j := by
    simp only [productSecondFibreHomeomorph_apply, j, k, f,
      Scheme.Hom.fiberι_fiberHomeo_symm, orbitSection_fst]
  have hj : k = j := (productSecondFibreHomeomorph H X x).injective he
  have hp := congrArg (f.fiberι (X.pointMap x)) hj
  simpa only [j, k, f, Scheme.Hom.fiberι_fiberHomeo_symm] using hp

private lemma relationFactor_second (t : (productVariety H X).scheme) :
    (snd X.toOver X.toOver).left
      ((orbitRelationInclusion H X).left ((orbitRelationFactor H X).left t)) =
        (ModObj.smul (M := H.toOver) (X := X.toOver)).left t := by
  have hs : (orbitRelationFactor H X ≫ orbitRelationInclusion H X) ≫
      snd X.toOver X.toOver = ModObj.smul (M := H.toOver) (X := X.toOver) := by
    rw [orbitRelationFactor_fac, orbitRelationMorphism, lift_snd]
  exact congrArg (fun f : (productVariety H X).toOver ⟶ X.toOver ↦ f.left t) hs

/-- The orbit morphism's image lies in the closed image of its relation fibre. -/
theorem orbitImage_subset_relationFibre (x : X.points) :
    Set.range (orbitMorphism H X x).left ⊆ Set.range (relationFibreMap H X x) := by
  rintro y ⟨h, rfl⟩
  let t := (orbitSection H X x).left h
  let r := (orbitRelationFactor H X).left t
  have hr : (orbitRelationProjection H X).left r = X.pointMap x := by
    have hf := congrArg
      (fun f : (productVariety H X).toOver ⟶ X.toOver ↦ f.left t)
      (orbitRelationProjection_fac H X)
    exact hf.trans (orbitSection_snd H X x h)
  let z := ((orbitRelationProjection H X).left.fiberHomeo (X.pointMap x)).symm ⟨r, hr⟩
  refine ⟨z, ?_⟩
  rw [relationFibreMap_apply]
  have hz : (orbitRelationProjection H X).left.fiberι (X.pointMap x) z = r :=
    (orbitRelationProjection H X).left.fiberι_fiberHomeo_symm _ _
  rw [hz]
  change (snd X.toOver X.toOver).left ((orbitRelationInclusion H X).left r) =
    (ModObj.smul (M := H.toOver) (X := X.toOver)).left t
  exact relationFactor_second H X t

/-- A relation-fibre point in the relation morphism's image maps into the orbit image. -/
theorem relationFibre_image_of_range (x : X.points)
    (z : (orbitRelationProjection H X).left.fiber (X.pointMap x))
    (hz : (orbitRelationProjection H X).left.fiberι (X.pointMap x) z ∈
      Set.range (orbitRelationFactor H X).left) :
    relationFibreMap H X x z ∈ Set.range (orbitMorphism H X x).left := by
  obtain ⟨t, ht⟩ := hz
  have htf : (snd H.toOver X.toOver).left t = X.pointMap x := by
    have hf := congrArg
      (fun f : (productVariety H X).toOver ⟶ X.toOver ↦ f.left t)
      (orbitRelationProjection_fac H X)
    change (orbitRelationProjection H X).left ((orbitRelationFactor H X).left t) =
      (snd H.toOver X.toOver).left t at hf
    rw [ht] at hf
    exact hf.symm.trans
      (((orbitRelationProjection H X).left.fiberHomeo (X.pointMap x) z).property)
  refine ⟨(fst H.toOver X.toOver).left t, ?_⟩
  rw [relationFibreMap_apply]
  have hs := relationFactor_second H X t
  rw [ht] at hs
  rw [hs]
  change (ModObj.smul (M := H.toOver) (X := X.toOver)).left
    ((orbitSection H X x).left ((fst H.toOver X.toOver).left t)) =
      (ModObj.smul (M := H.toOver) (X := X.toOver)).left t
  exact congrArg (ModObj.smul (M := H.toOver) (X := X.toOver)).left
    (eq_orbitSection H X x t htf)

/-- Orbit dimension is bounded by the dimension of the corresponding relation fibre. -/
theorem orbitDim_le_relationFibre (x : X.points) :
    orbitDim H X x ≤
      topologicalKrullDim ((orbitRelationProjection H X).left.fiber (X.pointMap x)) := by
  have hr : orbitClosure H X x ⊆ Set.range (relationFibreMap H X x) := by
    rw [orbitClosure_eq]
    exact closure_minimal (orbitImage_subset_relationFibre H X x)
      (relationFibreMap_isClosedEmbedding H X x).isClosed_range
  change topologicalKrullDim (orbitClosure H X x) ≤ _
  exact ((IsEmbedding.inclusion hr).isInducing.topologicalKrullDim_le).trans_eq
    (relationFibreMap_dim H X x)

end

end GroupActions.Variety
