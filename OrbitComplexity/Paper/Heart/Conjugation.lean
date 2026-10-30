import OrbitComplexity.Paper.Heart.Definition
import OrbitComplexity.GroupActions.Varieties.AffineAutomorphisms

/-!
# Conjugation from the minimal factor to the heart root group

The quotient Hopf coordinate isomorphism realizes Weyl-point conjugation as an
isomorphism between the minimal-factor root group and Vd.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits
open ReductiveGroups TauCeti GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
private theorem specSquare {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (e : B →+* C) (g : A →+* D) (h : D →+* C)
    (he : e.comp f = h.comp g) :
    Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom g) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ : A →+* C => Spec.map (CommRingCat.ofHom φ)) he

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact TauCeti.isReduced_of_smooth K G.coordinateAlgebra

attribute [local instance] coordinateReduced

/-- Coordinate conjugation gives the minimal-factor root group isomorphism onto Vd. -/
def minimalToVdIso (I : Set G.rootBase.support) (w : G.weylGroup) :
    (schubertUnipotent G (leftParabolicRepresentative G.rootBase I w)).toOver ≅
      (Vd.variety G I w).toOver :=
  affineGroupIso (Vd.coordinateConjugation G I w)

set_option backward.isDefEq.respectTransparency.types false in
/-- The minimal-root conjugation isomorphism commutes with ambient group conjugation. -/
theorem minimalToVdIso_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    (minimalToVdIso G I w).hom ≫
        rootSubsetInclusion G (heartRootIndices G I w) (heartRootIndices_closed G I w) =
      schubertUnipotentInclusion G (leftParabolicRepresentative G.rootBase I w) ≫
        (affineGroupIso (HopfAlgebra.pointConjugationBialgEquiv
          (G.weylPoint (leftParabolicFactor G.rootBase I w)))).hom := by
  have hc : (Vd.coordinateConjugation G I w).toAlgEquiv.toAlgHom.comp
      (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal (heartRootIndices G I w)
        (heartRootIndices_closed G I w)).toIdeal) =
    (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal
      (leftRootInversionIndices G.rootBase (leftParabolicRepresentative G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal).comp
      (HopfAlgebra.pointConjugationAlgHom
        (G.weylPoint (leftParabolicFactor G.rootBase I w))) := by
    apply AlgHom.ext
    intro b
    exact Vd.coordinateConjugation_mk G I w b
  apply Over.OverMorphism.ext
  exact specSquare _ _ _ _ (congrArg AlgHom.toRingHom hc)

omit [IsAlgClosed K] [CharZero K] in
private theorem ambientConjugation_points (g x : G.points) :
    Variety.mapPoints (affineGroupIso (HopfAlgebra.pointConjugationBialgEquiv g)).hom
      (reductivePointsEquiv G x) = reductivePointsEquiv G (g * x * g⁻¹) := by
  change Variety.mapPoints (affineGroupIso (HopfAlgebra.pointConjugationBialgEquiv g)).hom
    ((affineVarietyPointsEquiv K G.coordinateAlgebra).symm x.ofConv) =
      (affineVarietyPointsEquiv K G.coordinateAlgebra).symm (g * x * g⁻¹).ofConv
  rw [affineGroupIso_points]
  apply congrArg (affineVarietyPointsEquiv K G.coordinateAlgebra).symm
  change x.ofConv.comp ((HopfAlgebra.pointConjugationBialgEquiv g :
    G.coordinateAlgebra →ₐc[K] G.coordinateAlgebra) :
      G.coordinateAlgebra →ₐ[K] G.coordinateAlgebra) = _
  rw [HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  have h := congrArg WithConv.ofConv (HopfAlgebra.comp_pointConjugationAlgHom g x)
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl, AlgHom.mapValue_id,
    MonoidHom.id_apply, WithConv.ofConv_toConv] using h

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism from the minimal root group to Vd is Weyl-point conjugation. -/
theorem minimalToVdIso_points (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (schubertUnipotent G (leftParabolicRepresentative G.rootBase I w)).points) :
    (rootSubsetPointsMulEquiv G _ (heartRootIndices_closed G I w)
      (Variety.mapPoints (minimalToVdIso G I w).hom x) : G.points) =
        G.weylPoint (leftParabolicFactor G.rootBase I w) *
          (rootSubsetPointsMulEquiv G _
            (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) x : G.points) *
          (G.weylPoint (leftParabolicFactor G.rootBase I w))⁻¹ := by
  let g := G.weylPoint (leftParabolicFactor G.rootBase I w)
  let y : G.points := rootSubsetPointsMulEquiv G _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) x
  let v : G.points := rootSubsetPointsMulEquiv G _ (heartRootIndices_closed G I w)
    (Variety.mapPoints (minimalToVdIso G I w).hom x)
  let C : (reductiveVariety G).toOver ⟶ (reductiveVariety G).toOver :=
    (affineGroupIso (HopfAlgebra.pointConjugationBialgEquiv g)).hom
  have hC : Variety.mapPoints C (reductivePointsEquiv G y) =
      reductivePointsEquiv G (g * y * g⁻¹) := ambientConjugation_points G g y
  have hd : Variety.mapPoints (rootSubsetInclusion G _ (heartRootIndices_closed G I w))
      (Variety.mapPoints (minimalToVdIso G I w).hom x) =
      Variety.mapPoints C (Variety.mapPoints (schubertUnipotentInclusion G
        (leftParabolicRepresentative G.rootBase I w)) x) := by
    have h := congrArg (fun f : (schubertUnipotent G
      (leftParabolicRepresentative G.rootBase I w)).toOver ⟶
        (reductiveVariety G).toOver => Variety.mapPoints f x) (minimalToVdIso_comp G I w)
    exact (Variety.mapPoints_comp _ _ x).symm.trans
      (h.trans (Variety.mapPoints_comp _ _ x))
  have hleft : Variety.mapPoints (rootSubsetInclusion G _ (heartRootIndices_closed G I w))
      (Variety.mapPoints (minimalToVdIso G I w).hom x) = reductivePointsEquiv G v :=
    rootSubsetInclusion_points G _ _ _
  have hright : Variety.mapPoints (schubertUnipotentInclusion G
      (leftParabolicRepresentative G.rootBase I w)) x = reductivePointsEquiv G y :=
    rootSubsetInclusion_points G _ _ _
  exact (reductivePointsEquiv G).injective
    (hleft.symm.trans (hd.trans ((congrArg (Variety.mapPoints C) hright).trans hC)))

end SchubertOrbits
