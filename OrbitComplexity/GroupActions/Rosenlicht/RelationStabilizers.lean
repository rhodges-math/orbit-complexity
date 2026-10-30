import OrbitComplexity.GroupActions.Rosenlicht.OrbitFibreImages
import OrbitComplexity.GroupActions.Actions.Stabilizers

/-!
# Stabilizer fibres of the orbit relation map

The fibre of the orbit relation map over the diagonal point is homeomorphic
to the stabilizer. The product projection recovers the group parameter.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

private def parameterSection (x : X.points) : H.toOver ⟶ (productVariety H X).toOver :=
  lift (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x)

omit [GrpObj H.toOver] [ModObj H.toOver X.toOver] in
private lemma parameterSection_fst (x : X.points) (h : H.scheme) :
    (fst H.toOver X.toOver).left ((parameterSection H X x).left h) = h := by
  exact congrArg (fun f : H.toOver ⟶ H.toOver ↦ f.left h)
    (lift_fst (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x))

omit [GrpObj H.toOver] [ModObj H.toOver X.toOver] in
private lemma parameterSection_snd (x : X.points) (h : H.scheme) :
    (snd H.toOver X.toOver).left ((parameterSection H X x).left h) = X.pointMap x := by
  have hs := congrArg (fun f : H.toOver ⟶ X.toOver ↦ f.left h)
    (lift_snd (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x))
  apply hs.trans
  change x.val ((toUnit H.toOver).left h) = x.val (IsLocalRing.closedPoint K)
  exact congrArg x.val (Subsingleton.elim _ _)

omit [GrpObj H.toOver] [ModObj H.toOver X.toOver] in
private lemma eq_parameterSection (x : X.points) (t : (productVariety H X).scheme)
    (ht : (snd H.toOver X.toOver).left t = X.pointMap x) :
    (parameterSection H X x).left ((fst H.toOver X.toOver).left t) = t := by
  let f := (snd H.toOver X.toOver).left
  let j : f.fiber (X.pointMap x) := (f.fiberHomeo (X.pointMap x)).symm ⟨t, ht⟩
  let k : f.fiber (X.pointMap x) := (f.fiberHomeo (X.pointMap x)).symm
    ⟨(parameterSection H X x).left ((fst H.toOver X.toOver).left t),
      parameterSection_snd H X x _⟩
  have he : productSecondFibreHomeomorph H X x k = productSecondFibreHomeomorph H X x j := by
    simp only [productSecondFibreHomeomorph_apply, j, k, f,
      Scheme.Hom.fiberι_fiberHomeo_symm, parameterSection_fst]
  have hj : k = j := (productSecondFibreHomeomorph H X x).injective he
  have hp := congrArg (f.fiberι (X.pointMap x)) hj
  simpa only [j, k, f, Scheme.Hom.fiberι_fiberHomeo_symm] using hp

private lemma relation_first (t : (productVariety H X).scheme) :
    (fst X.toOver X.toOver).left
      ((orbitRelationInclusion H X).left ((orbitRelationFactor H X).left t)) =
        (snd H.toOver X.toOver).left t := by
  exact congrArg (fun f : (productVariety H X).toOver ⟶ X.toOver ↦ f.left t)
    (orbitRelationProjection_fac H X)

private lemma relation_second (t : (productVariety H X).scheme) :
    (snd X.toOver X.toOver).left
      ((orbitRelationInclusion H X).left ((orbitRelationFactor H X).left t)) =
        (ModObj.smul (M := H.toOver) (X := X.toOver)).left t := by
  have hs : (orbitRelationFactor H X ≫ orbitRelationInclusion H X) ≫
      snd X.toOver X.toOver = ModObj.smul (M := H.toOver) (X := X.toOver) := by
    rw [orbitRelationFactor_fac, orbitRelationMorphism, lift_snd]
  exact congrArg (fun f : (productVariety H X).toOver ⟶ X.toOver ↦ f.left t) hs

/-- The diagonal rational point of the orbit relation closure. -/
def relationDiagonalPoint (x : X.points) : (orbitRelationVariety H X).points :=
  mapPoints (parameterSection H X x ≫ orbitRelationFactor H X) 1

/-- The diagonal point has a rational preimage under the orbit relation map. -/
theorem relationDiagonalPoint_preimage (x : X.points) :
    ∃ p : (productVariety H X).points,
      mapPoints (orbitRelationFactor H X) p = relationDiagonalPoint H X x := by
  refine ⟨mapPoints (parameterSection H X x) 1, ?_⟩
  exact (mapPoints_comp (parameterSection H X x) (orbitRelationFactor H X) 1).symm

private lemma diagonal_first (x : X.points) :
    (fst X.toOver X.toOver).left ((orbitRelationInclusion H X).left
      ((orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x))) = X.pointMap x := by
  rw [relationDiagonalPoint, pointMap_mapPoints]
  exact (relation_first H X _).trans (parameterSection_snd H X x _)

private lemma diagonal_second (x : X.points) :
    (snd X.toOver X.toOver).left ((orbitRelationInclusion H X).left
      ((orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x))) = X.pointMap x := by
  rw [relationDiagonalPoint, pointMap_mapPoints]
  apply (relation_second H X _).trans
  change (orbitMorphism H X x).left (H.pointMap 1) = X.pointMap x
  rw [← pointMap_mapPoints, mapPoints_orbitMorphism, one_smul]

private lemma section_fibre_iff (x : X.points) (h : H.scheme) :
    (orbitRelationFactor H X).left ((parameterSection H X x).left h) =
        (orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x) ↔
      (orbitMorphism H X x).left h = X.pointMap x := by
  constructor
  · intro he
    have hs := congrArg
      (fun r ↦ (snd X.toOver X.toOver).left ((orbitRelationInclusion H X).left r)) he
    rw [relation_second, diagonal_second] at hs
    exact hs
  · intro hh
    apply (orbitRelationInclusion H X).left.isEmbedding.injective
    let a := (orbitRelationInclusion H X).left
      ((orbitRelationFactor H X).left ((parameterSection H X x).left h))
    let b := (orbitRelationInclusion H X).left
      ((orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x))
    have ha : (snd X.toOver X.toOver).left a = X.pointMap x :=
      (relation_second H X _).trans hh
    have hb : (snd X.toOver X.toOver).left b = X.pointMap x := diagonal_second H X x
    have hf : (fst X.toOver X.toOver).left a = (fst X.toOver X.toOver).left b := by
      exact ((relation_first H X _).trans (parameterSection_snd H X x _)).trans
        (diagonal_first H X x).symm
    change a = b
    rw [← eq_parameterSection X X x a ha, hf, eq_parameterSection X X x b hb]

private def stabilizerToRelationFibre (x : X.points) :
    (orbitMorphism H X x).left ⁻¹' {X.pointMap x} →
      (orbitRelationFactor H X).left ⁻¹'
        {(orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x)} :=
  fun h ↦ ⟨(parameterSection H X x).left h.val,
    (section_fibre_iff H X x h.val).mpr h.property⟩

private lemma stabilizerToRelationFibre_bijective (x : X.points) :
    Function.Bijective (stabilizerToRelationFibre H X x) := by
  constructor
  · intro h k he
    apply Subtype.ext
    exact (parameterSection_fst H X x h.val).symm.trans
      ((congrArg (fst H.toOver X.toOver).left (congrArg Subtype.val he)).trans
        (parameterSection_fst H X x k.val))
  · intro t
    have ht : (snd H.toOver X.toOver).left t.val = X.pointMap x := by
      have he := relation_first H X t.val
      rw [t.property] at he
      exact he.symm.trans (diagonal_first H X x)
    have he := eq_parameterSection H X x t.val ht
    have hm : (orbitMorphism H X x).left ((fst H.toOver X.toOver).left t.val) = X.pointMap x := by
      apply (section_fibre_iff H X x _).mp
      rw [he]
      exact t.property
    exact ⟨⟨(fst H.toOver X.toOver).left t.val, hm⟩, Subtype.ext he⟩

/-- The relation-map fibre at the diagonal point is homeomorphic to the stabilizer fibre. -/
def relationStabilizerHomeomorph (x : X.points) :
    (orbitRelationFactor H X).left.fiber
        ((orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x)) ≃ₜ
      (orbitMorphism H X x).left ⁻¹' {X.pointMap x} := by
  let s := parameterSection H X x
  have hs : IsEmbedding s.left := by
    apply IsEmbedding.of_leftInverse (f := (fst H.toOver X.toOver).left)
      (g := s.left) (parameterSection_fst H X x)
      (fst H.toOver X.toOver).left.continuous s.left.continuous
  have hmaps : Set.MapsTo s.left ((orbitMorphism H X x).left ⁻¹' {X.pointMap x})
      ((orbitRelationFactor H X).left ⁻¹'
        {(orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x)}) := by
    intro h hh
    exact (section_fibre_iff H X x h).mpr hh
  have he : IsEmbedding (stabilizerToRelationFibre H X x) := hs.restrict hmaps
  exact ((orbitRelationFactor H X).left.fiberHomeo _).trans
    (he.toHomeomorphOfSurjective (stabilizerToRelationFibre_bijective H X x).surjective).symm

/-- The relation-map fibre at a diagonal point has stabilizer dimension. -/
theorem relationStabilizer_dim (x : X.points) :
    topologicalKrullDim ((orbitRelationFactor H X).left.fiber
      ((orbitRelationVariety H X).pointMap (relationDiagonalPoint H X x))) =
        (stabilizerVariety H X x).dim :=
  (relationStabilizerHomeomorph H X x).isHomeomorph.topologicalKrullDim_eq.trans
    (stabilizerHomeomorph H X x).isHomeomorph.topologicalKrullDim_eq.symm

end

end GroupActions.Variety
