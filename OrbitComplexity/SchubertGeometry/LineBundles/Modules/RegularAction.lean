import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterLine
import OrbitComplexity.GroupActions.Actions.FromPoints
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct
import OrbitComplexity.GroupActions.Varieties.BorelPoints
import OrbitComplexity.GroupActions.Varieties.AdditiveVariety

/-! # The regular Borel action on its inverse-character line -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups GroupActions TauCeti CategoryTheory AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem borelReduced : IsReduced G.borelAlgebra := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact isReduced_of_smooth K G.borelAlgebra
omit [CharZero K] in
private theorem tensorReduced : IsReduced (G.borelAlgebra ⊗[K] SymmetricAlgebra K K) := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  let : Algebra.Smooth K (SymmetricAlgebra K K) := by infer_instance
  let : Algebra.Smooth K (G.borelAlgebra ⊗[K] SymmetricAlgebra K K) :=
    Algebra.Smooth.comp K G.borelAlgebra _
  exact isReduced_of_smooth K _
omit [CharZero K] in
private theorem tensorFinite :
    Algebra.FiniteType K (G.borelAlgebra ⊗[K] SymmetricAlgebra K K) := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  let : Algebra.Smooth K (SymmetricAlgebra K K) := by infer_instance
  let : Algebra.Smooth K (G.borelAlgebra ⊗[K] SymmetricAlgebra K K) :=
    Algebra.Smooth.comp K G.borelAlgebra _
  infer_instance
attribute [local instance] borelReduced tensorReduced tensorFinite

private def characterPointHom (chi : G.characters) : (borelVariety G).points →* Kˣ :=
  (borelCharacterUnit G chi).comp
    (affineGroupPointsMulEquiv K G.borelAlgebra).symm.toMonoidHom

@[instance_reducible]
private def characterPointAction (chi : G.characters) :
    MulAction (borelVariety G).points (additiveVariety K).points where
  smul b x := additivePointsEquiv K
    ((↑(characterPointHom G chi b)⁻¹ : K) * (additivePointsEquiv K).symm x)
  one_smul x := by
    change additivePointsEquiv K
      ((↑(characterPointHom G chi 1)⁻¹ : K) * (additivePointsEquiv K).symm x) = x
    rw [map_one, inv_one, Units.val_one, one_mul, Equiv.apply_symm_apply]
  mul_smul b c x := by
    change additivePointsEquiv K
      ((↑(characterPointHom G chi (b * c))⁻¹ : K) * (additivePointsEquiv K).symm x) =
        additivePointsEquiv K ((↑(characterPointHom G chi b)⁻¹ : K) *
          (additivePointsEquiv K).symm
            (additivePointsEquiv K
              ((↑(characterPointHom G chi c)⁻¹ : K) * (additivePointsEquiv K).symm x)))
    rw [(characterPointHom G chi).map_mul b c, mul_inv_rev, Units.val_mul,
      Equiv.symm_apply_apply]
    congr 1
    rw [mul_comm (↑(characterPointHom G chi c)⁻¹ : K), mul_assoc]

private def tensorIso :
    (affineVariety K (G.borelAlgebra ⊗[K] SymmetricAlgebra K K)).toOver ≅
      (borelVariety G).toOver ⊗ (additiveVariety K).toOver :=
  affineTensorIso K G.borelAlgebra (SymmetricAlgebra K K)

/-- The inverse-character polynomial defines a morphism from Borel times affine line. -/
def characterLineMorphism (chi : G.characters) :
    (borelVariety G).toOver ⊗ (additiveVariety K).toOver ⟶ (additiveVariety K).toOver :=
  (tensorIso G).inv ≫ affineMorphism (characterLineCoordinate G chi)

omit [CharZero K] in
private theorem pair_tensor (b : G.borelAlgebra →ₐ[K] K)
    (a : SymmetricAlgebra K K →ₐ[K] K) :
    lift ((affineVariety K G.borelAlgebra).pointsEquivOverHom (affinePointsEquiv b))
        ((affineVariety K (SymmetricAlgebra K K)).pointsEquivOverHom (affinePointsEquiv a)) ≫
        (tensorIso G).inv =
      (affineVariety K (G.borelAlgebra ⊗[K] SymmetricAlgebra K K)).pointsEquivOverHom
        (affinePointsEquiv (Algebra.TensorProduct.lift b a (fun _ _ => .all _ _))) := by
  let p := affinePointsEquiv (Algebra.TensorProduct.lift b a (fun _ _ => .all _ _))
  have hp := affineTensorIso_points K G.borelAlgebra (SymmetricAlgebra K K) p
  have hf : affineProductPointsEquiv K G.borelAlgebra (SymmetricAlgebra K K) p =
      (affinePointsEquiv b, affinePointsEquiv a) := by
    change (Equiv.prodCongr affinePointsEquiv affinePointsEquiv)
      ((tensorAlgebraPointsEquiv K G.borelAlgebra (SymmetricAlgebra K K))
        ((affinePointsEquiv).symm p)) = _
    simp only [p, Equiv.symm_apply_apply]
    change (Equiv.prodCongr affinePointsEquiv affinePointsEquiv)
      ((tensorAlgebraPointsEquiv K G.borelAlgebra (SymmetricAlgebra K K))
        ((tensorAlgebraPointsEquiv K G.borelAlgebra (SymmetricAlgebra K K)).symm (b, a))) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hf] at hp
  change lift ((affineVariety K G.borelAlgebra).pointsEquivOverHom (affinePointsEquiv b))
      ((affineVariety K (SymmetricAlgebra K K)).pointsEquivOverHom (affinePointsEquiv a)) ≫
      (tensorIso G).inv = _
  rw [← hp]
  simp only [Category.assoc, tensorIso, Iso.hom_inv_id, Category.comp_id]
  rfl

private theorem character_pair (chi : G.characters)
    (b : (borelVariety G).points) (a : (additiveVariety K).points) :
    letI := characterPointAction G chi
    lift ((borelVariety G).pointsEquivOverHom b)
      ((additiveVariety K).pointsEquivOverHom a) ≫ characterLineMorphism G chi =
      (additiveVariety K).pointsEquivOverHom (b • a) := by
  obtain ⟨b, rfl⟩ := (affineGroupPointsMulEquiv K G.borelAlgebra).surjective b
  obtain ⟨a, rfl⟩ := (additivePointsEquiv K).surjective a
  let c := (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd a)
  change (lift ((affineVariety K G.borelAlgebra).pointsEquivOverHom
      (affinePointsEquiv b.ofConv))
    ((affineVariety K (SymmetricAlgebra K K)).pointsEquivOverHom
      (affinePointsEquiv c.ofConv)) ≫ (tensorIso G).inv) ≫
    affineMorphism (characterLineCoordinate G chi) = _
  rw [pair_tensor]
  have he := characterLineCoordinate_eval G chi b a
  change (Algebra.TensorProduct.lift b.ofConv c.ofConv (fun _ _ => .all _ _)).comp
    (characterLineCoordinate G chi) = _ at he
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift b.ofConv c.ofConv (fun _ _ => .all _ _)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (characterLineCoordinate G chi).toRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((Algebra.TensorProduct.lift b.ofConv c.ofConv (fun _ _ => .all _ _)).comp
      (characterLineCoordinate G chi)).toRingHom)) = _
  rw [he]
  congr 2
  have hb : characterPointHom G chi (affineGroupPointsMulEquiv K G.borelAlgebra b) =
      borelCharacterUnit G chi b := by
    change borelCharacterUnit G chi
      ((affineGroupPointsMulEquiv K G.borelAlgebra).symm
        (affineGroupPointsMulEquiv K G.borelAlgebra b)) = _
    rw [MulEquiv.symm_apply_apply]
  simp only [Equiv.symm_apply_apply]
  change ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd ((↑(borelCharacterUnit G chi b)⁻¹ : K) * a))).ofConv.toRingHom =
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd ((↑(characterPointHom G chi
          (affineGroupPointsMulEquiv K G.borelAlgebra b))⁻¹ : K) * a))).ofConv.toRingHom
  rw [hb]

/-- The inverse-character line carries a regular action of the chosen Borel group. -/
@[instance_reducible]
def characterLineAction (chi : G.characters) :
    ModObj (borelVariety G).toOver (additiveVariety K).toOver := by
  letI := characterPointAction G chi
  apply Variety.modObjOfPoints (borelVariety G) (additiveVariety K)
    (characterLineMorphism G chi)
  intro b a
  exact character_pair G chi b a

/-- The regular fibre action evaluates the inverse of the same full Borel character. -/
theorem characterLineAction_smul (chi : G.characters)
    (b : (borelVariety G).points) (x : (additiveVariety K).points) :
    letI := characterLineAction G chi
    b • x = additivePointsEquiv K
      ((↑(borelCharacterUnit G chi
        ((affineGroupPointsMulEquiv K G.borelAlgebra).symm b))⁻¹ : K) *
          (additivePointsEquiv K).symm x) := by
  let := characterLineAction G chi
  apply (additiveVariety K).pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_smul]
  change lift ((borelVariety G).pointsEquivOverHom b)
    ((additiveVariety K).pointsEquivOverHom x) ≫ characterLineMorphism G chi = _
  exact character_pair G chi b x

end SchubertGeometry.ProjectiveLine
