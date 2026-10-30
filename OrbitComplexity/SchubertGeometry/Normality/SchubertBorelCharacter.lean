import OrbitComplexity.SchubertGeometry.Parabolics.EmptyLevi
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionProjection
import OrbitComplexity.SchubertGeometry.Parabolics.BorelInclusion
import OrbitComplexity.ReductiveGroups.Groups.Reductive.TorusData

/-! # Characters of the Borel from the regular torus projection -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti Opposite
universe u v w
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact isReduced_of_smooth K G.coordinateAlgebra

omit [CharZero K] in
private theorem borelReduced :
    IsReduced (G.coordinateAlgebra ⧸ G.borelIdeal.toIdeal) := by
  change IsReduced G.borelAlgebra
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact isReduced_of_smooth K G.borelAlgebra

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced :
    IsReduced (G.coordinateAlgebra ⧸ G.torusIdeal.toIdeal) := by
  change IsReduced G.torusAlgebra
  let : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact isReduced_of_smooth K G.torusAlgebra

attribute [local instance] coordinateReduced borelReduced torusReduced

private def torusBorel : (torusVariety G).toOver ⟶ (borelVariety G).toOver :=
  closedSubgroupMap G.coordinateAlgebra G.borelIdeal G.torusIdeal G.borel_le_torus

private instance torusBorel_mon : IsMonHom (torusBorel G) := by
  unfold torusBorel
  exact closedSubgroupMap_isMonHom G.coordinateAlgebra G.borelIdeal G.torusIdeal
    G.borel_le_torus

omit [CharZero K] in
private theorem torusBorel_comp :
    torusBorel G ≫ borelInclusion G = torusInclusion G :=
  closedSubgroupMap_comp_inclusion _ _ _ _

private def torusLevi : (torusVariety G).toOver ⟶ (leviVariety G ∅).toOver :=
  torusLeviBorelInclusion G ∅ ≫ leviBorelLeviInclusion G ∅

private instance torusLevi_iso : IsIso (torusLevi G) :=
  (emptyLevi_isTorus G).2.2.2

private instance torusLevi_mon : IsMonHom (torusLevi G) := by
  unfold torusLevi
  infer_instance

private theorem torusBorel_parabolic :
    torusBorel G ≫ borelParabolicInclusion G ∅ =
      torusLevi G ≫ leviParabolicInclusion G ∅ := by
  have : Mono (standardParabolicInclusion G ∅) := Over.mono_of_mono_left _
  apply (cancel_mono (standardParabolicInclusion G ∅)).mp
  simp only [Category.assoc, borelParabolic_comp, leviParabolicInclusion_comp]
  rw [torusBorel_comp]
  unfold torusLevi
  rw [Category.assoc, leviBorelLeviInclusion_comp, torusLeviBorelInclusion_comp]

private def borelProjection : (borelVariety G).toOver ⟶ (torusVariety G).toOver :=
  borelParabolicInclusion G ∅ ≫ parabolicLeviProjection G ∅ ≫ (asIso (torusLevi G)).inv

private instance borelProjection_mon : IsMonHom (borelProjection G) := by
  unfold borelProjection
  infer_instance

private theorem borelProjection_section :
    torusBorel G ≫ borelProjection G = 𝟙 (torusVariety G).toOver := by
  unfold borelProjection
  rw [← Category.assoc, ← Category.assoc, torusBorel_parabolic]
  simp only [Category.assoc, parabolicLeviProjection_section, Category.id_comp]
  exact (asIso (torusLevi G)).hom_inv_id

private def projectionGrp :
    (hopfSpec (CommRingCat.of K)).obj (op (CommHopfAlgCat.of K G.borelAlgebra)) ⟶
      (hopfSpec (CommRingCat.of K)).obj (op (CommHopfAlgCat.of K G.torusAlgebra)) := by
  exact @Grp.homMk _ _ _ _ _ (borelProjection G) (borelProjection_mon G)

private def projectionMap : G.torusAlgebra →ₐc[K] G.borelAlgebra :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimage (projectionGrp G)).unop.hom

private theorem projectionMap_spec :
    ((hopfSpec (CommRingCat.of K)).map (CommHopfAlgCat.ofHom (projectionMap G)).op).hom.hom =
      borelProjection G := by
  have hf : (CommHopfAlgCat.ofHom (projectionMap G)).op =
      (hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimage (projectionGrp G) := by
    unfold projectionMap
    rw [CommHopfAlgCat.ofHom_hom, Quiver.Hom.op_unop]
  rw [hf]
  have h := (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage (projectionGrp G)
  exact congrArg (fun f :
    (hopfSpec (CommRingCat.of K)).obj (op (CommHopfAlgCat.of K G.borelAlgebra)) ⟶
      (hopfSpec (CommRingCat.of K)).obj (op (CommHopfAlgCat.of K G.torusAlgebra)) =>
        f.hom.hom) h

private def torusRestriction : G.borelAlgebra →ₐc[K] G.torusAlgebra :=
  (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj G.borel_le_torus).hom

omit [CharZero K] in
private theorem torusRestriction_spec :
    ((hopfSpec (CommRingCat.of K)).map
      (CommHopfAlgCat.ofHom (torusRestriction G)).op).hom.hom = torusBorel G := by
  unfold torusRestriction
  rw [CommHopfAlgCat.ofHom_hom]
  rfl

private theorem projectionMap_section :
    (torusRestriction G).comp (projectionMap G) = BialgHom.id K G.torusAlgebra := by
  have h : (hopfSpec (CommRingCat.of K)).map
      (CommHopfAlgCat.ofHom (torusRestriction G)).op ≫
      (hopfSpec (CommRingCat.of K)).map (CommHopfAlgCat.ofHom (projectionMap G)).op =
      𝟙 ((hopfSpec (CommRingCat.of K)).obj (op (CommHopfAlgCat.of K G.torusAlgebra))) := by
    apply (Grp.forget (Over (Spec (CommRingCat.of K)))).map_injective
    change ((hopfSpec (CommRingCat.of K)).map
      (CommHopfAlgCat.ofHom (torusRestriction G)).op).hom.hom ≫
      ((hopfSpec (CommRingCat.of K)).map (CommHopfAlgCat.ofHom (projectionMap G)).op).hom.hom =
        𝟙 (torusVariety G).toOver
    rw [torusRestriction_spec G, projectionMap_spec G]
    exact borelProjection_section G
  have hm : (hopfSpec (CommRingCat.of K)).map
      (CommHopfAlgCat.ofHom ((torusRestriction G).comp (projectionMap G))).op =
      (hopfSpec (CommRingCat.of K)).map
        (𝟙 (op (CommHopfAlgCat.of K G.torusAlgebra))) := by
    rw [CommHopfAlgCat.ofHom_comp, op_comp, CategoryTheory.Functor.map_comp, h,
      CategoryTheory.Functor.map_id]
  have hh := (hopfSpec.fullyFaithful (R := CommRingCat.of K)).map_injective hm
  exact congrArg (fun f :
    op (CommHopfAlgCat.of K G.torusAlgebra) ⟶ op (CommHopfAlgCat.of K G.torusAlgebra) =>
      f.unop.hom) hh

omit [IsAlgClosed K] [CharZero K] in
private def characterCoordinate {M : Type v} [CommGroup M] (chi : M) :
    MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] MonoidAlgebra K M :=
  MonoidAlgebra.mapDomainBialgHom K (zpowersHom M chi)

omit [IsAlgClosed K] [CharZero K] in
private theorem characterCoordinate_generator {M : Type v} [CommGroup M] (chi : M) :
    characterCoordinate (K := K) chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
      MonoidAlgebra.single chi 1 := by
  simp only [characterCoordinate, MonoidAlgebra.mapDomainBialgHom_single, zpowersHom_apply]
  change MonoidAlgebra.single (chi ^ (1 : ℤ)) 1 = MonoidAlgebra.single chi 1
  rw [zpow_one]

/-- The fixed torus splitting descends to its quotient coordinate algebra. -/
def torusCharacterCoordinates : G.torusAlgebra →ₐc[K] MonoidAlgebra K G.characters :=
  Bialgebra.Quotient.liftBialgHom G.torusIdeal.toIdeal G.torusSplit
    (fun a ha => (G.split_eq_zero a).mpr ha)

omit [IsAlgClosed K] [CharZero K] in
private def torusSplitEquiv : G.torusAlgebra ≃ₐc[K] MonoidAlgebra K G.characters :=
  BialgEquiv.ofBijective (torusCharacterCoordinates G) ⟨by
    have hk (a : G.torusAlgebra) : torusCharacterCoordinates G a = 0 ↔ a = 0 := by
      refine Quotient.inductionOn' a (fun a => ?_)
      change G.torusSplit a = 0 ↔ Ideal.Quotient.mk G.torusIdeal.toIdeal a = 0
      rw [G.split_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    intro a b hab
    apply sub_eq_zero.mp
    apply (hk (a - b)).mp
    exact (map_sub (torusCharacterCoordinates G) a b).trans
      (by rw [hab, sub_self]), by
    intro y
    obtain ⟨a, ha⟩ := G.split_surjective y
    exact ⟨Ideal.Quotient.mk G.torusIdeal.toIdeal a, ha⟩⟩

/-- The regular projection from the Borel to its torus, on coordinate Hopf algebras. -/
def borelTorusProjectionMap : G.torusAlgebra →ₐc[K] G.borelAlgebra := projectionMap G

/-- A torus character gives a morphism to the multiplicative group. -/
def torusCharacterMap (chi : G.characters) :
    MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] G.torusAlgebra :=
  (torusSplitEquiv G).symm.toBialgHom.comp (characterCoordinate (K := K) chi)

omit [IsAlgClosed K] [CharZero K] in
/-- Over every coefficient algebra, the torus morphism evaluates the specified character. -/
theorem torusCharacterMap_points {A : Type v} [CommRing A] [Algebra K A]
    (chi : G.characters) (z : MonoidAlgebra K G.characters →ₐ[K] A) :
    ((z.comp (torusCharacterCoordinates G).toAlgHom).comp (torusCharacterMap G chi).toAlgHom)
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
      z (MonoidAlgebra.single chi 1) := by
  change z ((torusSplitEquiv G) ((torusSplitEquiv G).symm
    (characterCoordinate (K := K) chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))) = _
  rw [(torusSplitEquiv G).apply_symm_apply, characterCoordinate_generator]

/-- Every torus character extends regularly to the Borel through its Levi projection. -/
def borelCharacterMap (chi : G.characters) :
    MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] G.borelAlgebra :=
  (borelTorusProjectionMap G).comp (torusCharacterMap G chi)

/-- Restriction along the torus inclusion recovers the given character morphism. -/
theorem borelCharacterMap_restrict (chi : G.characters) :
    (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj G.borel_le_torus).hom.comp
      (borelCharacterMap G chi) = torusCharacterMap G chi := by
  apply BialgHom.ext
  intro a
  exact congrArg (fun f : G.torusAlgebra →ₐc[K] G.torusAlgebra =>
    f (torusCharacterMap G chi a)) (projectionMap_section G)

/-- The extension evaluates every character on the projected torus over any algebra. -/
theorem borelCharacterMap_points {A : Type v} [CommRing A] [Algebra K A]
    (b : G.borelAlgebra →ₐ[K] A) :
    ∃ z : MonoidAlgebra K G.characters →ₐ[K] A,
      z.comp (torusCharacterCoordinates G).toAlgHom =
        b.comp (borelTorusProjectionMap G).toAlgHom ∧
      ∀ chi : G.characters,
        (b.comp (borelCharacterMap G chi).toAlgHom)
            (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
          z (MonoidAlgebra.single chi 1) := by
  refine ⟨(b.comp (borelTorusProjectionMap G).toAlgHom).comp
    (torusSplitEquiv G).symm.toAlgEquiv.toAlgHom, ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    change b (borelTorusProjectionMap G ((torusSplitEquiv G).symm
      ((torusSplitEquiv G) a))) = b (borelTorusProjectionMap G a)
    exact congrArg (fun x : G.torusAlgebra => b (borelTorusProjectionMap G x))
      ((torusSplitEquiv G).symm_apply_apply a)
  · intro chi
    change b (borelTorusProjectionMap G ((torusSplitEquiv G).symm
      (characterCoordinate (K := K) chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))) =
      b (borelTorusProjectionMap G ((torusSplitEquiv G).symm (MonoidAlgebra.single chi 1)))
    rw [characterCoordinate_generator]

end SchubertGeometry
