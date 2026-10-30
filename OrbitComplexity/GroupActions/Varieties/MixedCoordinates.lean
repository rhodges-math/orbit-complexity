import OrbitComplexity.GroupActions.Varieties.CoordinateLocalization
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.ReductiveGroups.Groups.Reductive.TorusData
import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Mixed torus and affine coordinates

Requiring selected affine coordinates to be nonzero gives a product of a split
torus and affine space in the remaining coordinates. The isomorphism preserves
the ambient coordinate functions.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable (K : Type u) [Field K] {ι : Type u} [Finite ι] (S : Finset ι)

private abbrev torusRing := MonoidAlgebra K (Multiplicative (S →₀ ℤ))
private abbrev affineRing := MvPolynomial {j // j ∉ S} K
private abbrev productRing := torusRing K S ⊗[K] affineRing K S
private abbrev polynomial := ∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K)

private instance torusReduced : IsReduced (torusRing K S) := by
  have : Algebra.Smooth K (torusRing K S) :=
    (ReductiveGroups.SplitTorus.groupData K S).reductive.smooth
  exact TauCeti.isReduced_of_smooth K (torusRing K S)

private instance productReduced : IsReduced (productRing K S) :=
  isReduced_of_injective (coordinateLocalizationEquiv K S).symm.toRingHom
    (coordinateLocalizationEquiv K S).symm.injective

private instance productFiniteType : Algebra.FiniteType K (productRing K S) :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (torusRing K S))
    (inferInstance : Algebra.FiniteType (torusRing K S) (productRing K S))

private def basicOpenOverIso :
    ((affineSpaceVariety K ι).openSubvariety
      (PrimeSpectrum.basicOpen (polynomial K S))).toOver ≅
        (Spec (.of (Localization.Away (polynomial K S)))).asOver (Spec (.of K)) := by
  let D : (Spec (.of (MvPolynomial ι K))).Opens :=
    PrimeSpectrum.basicOpen (polynomial K S)
  refine Over.isoMk
    (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial ι K)) (polynomial K S)) ?_
  change (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial ι K))
    (polynomial K S)).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away (polynomial K S)))) =
    D.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K)))
  have ht : Spec.map (CommRingCat.ofHom
        (algebraMap K (Localization.Away (polynomial K S)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial ι K) (Localization.Away (polynomial K S)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K))) := by
    rw [← Spec.map_comp]
    congr 2
  rw [ht, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]

private def localizationProductIso :
    (Spec (.of (Localization.Away (polynomial K S)))).asOver (Spec (.of K)) ≅
      (affineVariety K (productRing K S)).toOver :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (coordinateLocalizationEquiv K S).symm).op

/-- The open locus of nonzero selected coordinates is a split torus times affine space. -/
def mixedCoordinateIso :
    ((affineSpaceVariety K ι).openSubvariety
      (PrimeSpectrum.basicOpen (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K)))).toOver ≅
        (reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).toOver ⊗
          (affineSpaceVariety K {j // j ∉ S}).toOver :=
  basicOpenOverIso K S ≪≫ localizationProductIso K S ≪≫
    affineTensorIso K (torusRing K S) (affineRing K S)

private def coordinateMap : MvPolynomial ι K →ₐ[K] productRing K S :=
  (coordinateLocalizationEquiv K S).toAlgHom.comp
    (IsScalarTower.toAlgHom K (MvPolynomial ι K) (Localization.Away (polynomial K S)))

private theorem mixedCoordinateIso_inv_left :
    (mixedCoordinateIso K S).inv.left =
      (affineTensorIso K (torusRing K S) (affineRing K S)).inv.left ≫
        Spec.map (CommRingCat.ofHom (coordinateLocalizationEquiv K S).toRingHom) ≫
          (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial ι K))
            (polynomial K S)).inv := by
  simp only [mixedCoordinateIso, Iso.trans_inv, Over.comp_left]
  rfl

/-- The inverse mixed-coordinate chart followed by inclusion is the localization coordinate map. -/
theorem mixedCoordinateIso_inv_comp :
    (mixedCoordinateIso K S).inv ≫
        (affineSpaceVariety K ι).openInclusion
          (PrimeSpectrum.basicOpen (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K))) =
      (affineTensorIso K (MonoidAlgebra K (Multiplicative (S →₀ ℤ)))
        (MvPolynomial {j // j ∉ S} K)).inv ≫
          affineMorphism ((coordinateLocalizationEquiv K S).toAlgHom.comp
            (IsScalarTower.toAlgHom K (MvPolynomial ι K)
              (Localization.Away (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K))))) := by
  let D : (Spec (.of (MvPolynomial ι K))).Opens :=
    PrimeSpectrum.basicOpen (polynomial K S)
  let e : D.toScheme ≅ Spec (.of (Localization.Away (polynomial K S))) :=
    basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial ι K)) (polynomial K S)
  let t : ((affineVariety K (torusRing K S)).toOver ⊗
      (affineVariety K (affineRing K S)).toOver).left ⟶
        Spec (.of (productRing K S)) :=
    (affineTensorIso K (torusRing K S) (affineRing K S)).inv.left
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (MvPolynomial ι K) (Localization.Away (polynomial K S)))) = D.ι :=
    basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of (MvPolynomial ι K))
      (polynomial K S)
  have hb : e.inv ≫ D.ι = Spec.map (CommRingCat.ofHom
      (algebraMap (MvPolynomial ι K) (Localization.Away (polynomial K S)))) := by
    rw [← he, Iso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, mixedCoordinateIso_inv_left, Over.comp_left]
  change (t ≫ Spec.map (CommRingCat.ofHom (coordinateLocalizationEquiv K S).toRingHom) ≫
    e.inv) ≫ D.ι =
      t ≫ Spec.map (CommRingCat.ofHom (coordinateMap K S).toRingHom)
  simp only [Category.assoc]
  rw [hb, ← Spec.map_comp]
  rfl

private theorem affineCoordinate {B : Type u} [CommRing B] [Algebra K B]
    [IsReduced B] [Algebra.FiniteType K B] (f : MvPolynomial ι K →ₐ[K] B)
    (p : (affineVariety K B).points) (j : ι) :
    affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints (affineMorphism f) p) j =
      affineVarietyPointsEquiv K B p (f (MvPolynomial.X j)) := by
  obtain ⟨g, rfl⟩ := affinePointsEquiv.surjective p
  have hg : affineVarietyPointsEquiv K B (affinePointsEquiv g) = g :=
    Equiv.symm_apply_apply _ _
  calc
    _ = affineSpaceVarietyPointsEquiv K ι
        ((affineVarietyPointsEquiv K (MvPolynomial ι K)).symm (g.comp f)) j :=
      congrArg (fun p : (affineVariety K (MvPolynomial ι K)).points ↦
        affineSpaceVarietyPointsEquiv K ι p j) (affineMorphism_points f g)
    _ = g (f (MvPolynomial.X j)) := by
      change (affinePointsEquiv.symm (affinePointsEquiv (g.comp f))) (MvPolynomial.X j) = _
      rw [Equiv.symm_apply_apply]
      rfl
    _ = _ := congrArg (fun h : B →ₐ[K] K ↦ h (f (MvPolynomial.X j))) hg.symm

private def mixedPoint
    (t : (reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).points)
    (a : (affineSpaceVariety K {j // j ∉ S}).points) : (affineSpaceVariety K ι).points :=
  (affineSpaceVariety K ι).pointsEquivOverHom.symm
    (lift ((reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).pointsEquivOverHom t)
      ((affineSpaceVariety K {j // j ∉ S}).pointsEquivOverHom a) ≫
        (mixedCoordinateIso K S).inv ≫
          (affineSpaceVariety K ι).openInclusion
            (PrimeSpectrum.basicOpen (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K))))

private theorem mixedPoint_coordinate
    (t : (reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).points)
    (a : (affineSpaceVariety K {j // j ∉ S}).points) (j : ι) :
    affineSpaceVarietyPointsEquiv K ι (mixedPoint K S t a) j =
      (tensorAlgebraPointsEquiv K (torusRing K S) (affineRing K S)).symm
        (affineVarietyPointsEquiv K (torusRing K S) t,
          affineVarietyPointsEquiv K (affineRing K S) a)
            (coordinateMap K S (MvPolynomial.X j)) := by
  let f := (tensorAlgebraPointsEquiv K (torusRing K S) (affineRing K S)).symm
    (affineVarietyPointsEquiv K (torusRing K S) t,
      affineVarietyPointsEquiv K (affineRing K S) a)
  let q : (affineVariety K (productRing K S)).points := affinePointsEquiv f
  have hpair : affineProductPointsEquiv K (torusRing K S) (affineRing K S) q = (t, a) := by
    simp only [affineProductPointsEquiv, q, f, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply,
      affineVarietyPointsEquiv]
    exact Prod.ext (affinePointsEquiv.apply_symm_apply t) (affinePointsEquiv.apply_symm_apply a)
  have hq : (affineVariety K (productRing K S)).pointsEquivOverHom q ≫
      (affineTensorIso K (torusRing K S) (affineRing K S)).hom =
        lift ((reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).pointsEquivOverHom t)
          ((affineSpaceVariety K {j // j ∉ S}).pointsEquivOverHom a) := by
    rw [affineTensorIso_points, hpair]
    rfl
  have hx : mixedPoint K S t a = Variety.mapPoints (affineMorphism (coordinateMap K S)) q := by
    let A := affineVariety K (torusRing K S)
    let B := affineVariety K (affineRing K S)
    let P := affineVariety K (MvPolynomial ι K)
    let D : P.scheme.Opens := PrimeSpectrum.basicOpen (polynomial K S)
    let e : (P.openSubvariety D).toOver ≅ A.toOver ⊗ B.toOver := mixedCoordinateIso K S
    let i : (P.openSubvariety D).toOver ⟶ P.toOver := P.openInclusion D
    let u : Over.mk (𝟙 (Spec (.of K))) ⟶ A.toOver :=
      (reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).pointsEquivOverHom t
    let v : Over.mk (𝟙 (Spec (.of K))) ⟶ B.toOver :=
      (affineSpaceVariety K {j // j ∉ S}).pointsEquivOverHom a
    have he : e.inv ≫ i =
        (affineTensorIso K (torusRing K S) (affineRing K S)).inv ≫
          affineMorphism (coordinateMap K S) := mixedCoordinateIso_inv_comp K S
    have hq' : (affineVariety K (productRing K S)).pointsEquivOverHom q ≫
        (affineTensorIso K (torusRing K S) (affineRing K S)).hom = lift u v := hq
    have h : lift u v ≫ e.inv ≫ i =
        (affineVariety K (productRing K S)).pointsEquivOverHom q ≫
          affineMorphism (coordinateMap K S) := by
      rw [he, ← hq', Category.assoc, Iso.hom_inv_id_assoc]
    apply (affineSpaceVariety K ι).pointsEquivOverHom.injective
    exact h
  calc
    _ = affineSpaceVarietyPointsEquiv K ι
        (Variety.mapPoints (affineMorphism (coordinateMap K S)) q) j :=
      congrArg (fun p : (affineSpaceVariety K ι).points ↦
        affineSpaceVarietyPointsEquiv K ι p j) hx
    _ = affineVarietyPointsEquiv K (productRing K S) q
        (coordinateMap K S (MvPolynomial.X j)) := affineCoordinate K _ q j
    _ = _ := by
      change (affinePointsEquiv.symm (affinePointsEquiv f)) _ = f _
      rw [Equiv.symm_apply_apply]

/-- The inverse chart recovers selected torus characters and unselected affine coordinates. -/
theorem mixedCoordinateIso_points
    (t : (reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).points)
    (a : (affineSpaceVariety K {j // j ∉ S}).points) :
    let x := (affineSpaceVariety K ι).pointsEquivOverHom.symm
      (lift ((reductiveVariety (ReductiveGroups.SplitTorus.groupData K S)).pointsEquivOverHom t)
        ((affineSpaceVariety K {j // j ∉ S}).pointsEquivOverHom a) ≫
          (mixedCoordinateIso K S).inv ≫
            (affineSpaceVariety K ι).openInclusion
              (PrimeSpectrum.basicOpen (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K))))
    (∀ j : S, affineSpaceVarietyPointsEquiv K ι x j.val =
      affineVarietyPointsEquiv K (MonoidAlgebra K (Multiplicative (S →₀ ℤ))) t
        (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single j (1 : ℤ))) 1)) ∧
      (∀ j : {j // j ∉ S}, affineSpaceVarietyPointsEquiv K ι x j.val =
        affineSpaceVarietyPointsEquiv K {j // j ∉ S} a j) := by
  change (∀ j : S, affineSpaceVarietyPointsEquiv K ι (mixedPoint K S t a) j.val = _) ∧
    (∀ j : {j // j ∉ S}, affineSpaceVarietyPointsEquiv K ι (mixedPoint K S t a) j.val = _)
  constructor
  · intro j
    calc
      _ = (tensorAlgebraPointsEquiv K (torusRing K S) (affineRing K S)).symm
          (affineVarietyPointsEquiv K (torusRing K S) t,
            affineVarietyPointsEquiv K (affineRing K S) a)
              (coordinateMap K S (MvPolynomial.X j.val)) := mixedPoint_coordinate K S t a j.val
      _ = _ := by
        change (tensorAlgebraPointsEquiv K (torusRing K S) (affineRing K S)).symm
          (affineVarietyPointsEquiv K (torusRing K S) t,
            affineVarietyPointsEquiv K (affineRing K S) a)
              (coordinateLocalizationEquiv K S (algebraMap _ _ (MvPolynomial.X j.val))) = _
        rw [coordinateLocalization_X_mem, tensorAlgebraPointsEquiv_symm_tmul, map_one, mul_one]
  · intro j
    calc
      _ = (tensorAlgebraPointsEquiv K (torusRing K S) (affineRing K S)).symm
          (affineVarietyPointsEquiv K (torusRing K S) t,
            affineVarietyPointsEquiv K (affineRing K S) a)
              (coordinateMap K S (MvPolynomial.X j.val)) := mixedPoint_coordinate K S t a j.val
      _ = _ := by
        change (tensorAlgebraPointsEquiv K (torusRing K S) (affineRing K S)).symm
          (affineVarietyPointsEquiv K (torusRing K S) t,
            affineVarietyPointsEquiv K (affineRing K S) a)
              (coordinateLocalizationEquiv K S (algebraMap _ _ (MvPolynomial.X j.val))) =
          affineVarietyPointsEquiv K (affineRing K S) a (MvPolynomial.X j)
        rw [coordinateLocalization_X_not_mem, tensorAlgebraPointsEquiv_symm_tmul,
          map_one, one_mul]

end

end GroupActions
