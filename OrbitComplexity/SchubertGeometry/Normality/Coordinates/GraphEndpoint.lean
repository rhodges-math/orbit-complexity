import Batteries.Tactic.Lint
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons
import OrbitComplexity.SchubertGeometry.BSDH.RichardsonMap

/-! # Coordinate injections from the paired endpoint

Every patch is the inverse image of the prescribed flag patch. A finite affine
cover is chosen once on its paired-source preimage. Pullback of sections
along those exact chart legs is injective by surjectivity and target reducedness.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

universe u v

private theorem finiteType_pi (K : Type u) [CommRing K] (I : Type v) [Finite I] :
    ∀ (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
      [∀ i, Algebra.FiniteType K (B i)], Algebra.FiniteType K (∀ i, B i) := by
  classical
  refine Finite.induction_empty_option
    (P := fun I ↦ ∀ (B : I → Type u) [∀ i, CommRing (B i)]
      [∀ i, Algebra K (B i)] [∀ i, Algebra.FiniteType K (B i)],
        Algebra.FiniteType K (∀ i, B i)) ?_ ?_ ?_ I
  · intro I J e ih B _ _ _
    have : Algebra.FiniteType K (∀ i, B (e i)) := ih (fun i ↦ B (e i))
    exact Algebra.FiniteType.equiv inferInstance (AlgEquiv.piCongrLeft K B e)
  · intro B _ _ _
    infer_instance
  · intro I _ ih B _ _ _
    have : Algebra.FiniteType K (∀ i, B (some i)) := ih (fun i ↦ B (some i))
    let e : (∀ i, B i) ≃ₐ[K] (B none × ∀ i, B (some i)) :=
      { RingEquiv.piOptionEquivProd with commutes' _ := rfl }
    exact Algebra.FiniteType.equiv inferInstance e.symm

/-- Pullback along the legs of an open cover, as one algebra map into
the product of the chart coordinate rings. -/
def affineCoverSectionMap {K : Type u} [CommRing K]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (V : X.left.OpenCover) :
    ((algΓ (.of K)).obj Y).unop →ₐ[K]
      ∀ j, ((algΓ (.of K)).obj (Over.mk (V.f j ≫ X.hom))).unop :=
  AlgHom.pi fun j ↦ ((algΓ (.of K)).map
    (Over.homMk (V.f j ≫ f.left) (by
      change (V.f j ≫ f.left) ≫ Y.hom = V.f j ≫ X.hom
      rw [Category.assoc, f.w]) :
      Over.mk (V.f j ≫ X.hom) ⟶ Y)).unop.hom

private theorem affineCoverSectionMap_injective {K : Type u} [CommRing K]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (V : X.left.OpenCover)
    [QuasiCompact f.left] [Surjective f.left] [IsReduced Y.left] :
    Function.Injective (affineCoverSectionMap f V) := by
  let : IsSchemeTheoreticallyDominant f.left :=
    IsSchemeTheoreticallyDominant.of_isDominant f.left
  intro a b h
  apply f.left.app_injective ⊤
  apply V.ext_elem
  intro j
  exact congrFun h j

private theorem coordinates_finiteType {K : Type u} [CommRing K]
    (X : Over (Spec (.of K))) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    Algebra.FiniteType K ((algΓ (.of K)).obj X).unop := by
  let A := ((algΓ (.of K)).obj X).unop
  let η := (algΓAlgSpecAdjunction (.of K)).unit.app X
  let : IsIso η := coordinates_unit_isIso (.of K) X
  have : IsIso (inv η).left := by
    change IsIso ((Over.forget (Spec (.of K))).map (inv η))
    infer_instance
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      (inv η).left ≫ X.hom := (inv η).w.symm
  have hopen : IsOpenImmersion (inv η).left := inferInstance
  have hleft : LocallyOfFiniteType (inv η).left :=
    @locallyOfFiniteType_of_isOpenImmersion _ _ (inv η).left hopen
  have hft : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [hbase]
    exact @locallyOfFiniteType_comp _ _ _ (inv η).left X.hom hleft inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (φ := CommRingCat.ofHom (algebraMap K A))).mp hft

private theorem affine_endpoint_charts {K : Type u} [CommRing K]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y)
    [IsProper f.left] [Surjective f.left] [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] {T : Type u} [Finite T]
    (W : T → Y.left.Opens) (hW : ∀ t, IsAffineOpen (W t))
    (hcover : (⨆ t, W t) = ⊤) :
    ∃ V : ∀ t, (f.left ⁻¹ᵁ W t).toScheme.OpenCover.{u},
      Finite T ∧ (⨆ t, W t) = ⊤ ∧ (∀ t, Finite (V t).I₀) ∧
      (∀ t j, IsAffine ((V t).X j)) ∧
      ∀ t,
        let target := Over.mk ((W t).ι ≫ Y.hom)
        let source := Over.mk ((f.left ∣_ W t) ≫ target.hom)
        let q : source ⟶ target := Over.homMk (f.left ∣_ W t) rfl
        Algebra.FiniteType K ((algΓ (.of K)).obj target).unop ∧
        (∀ j, Algebra.FiniteType K
          ((algΓ (.of K)).obj (Over.mk ((V t).f j ≫ source.hom))).unop) ∧
        Algebra.FiniteType K (∀ j,
          ((algΓ (.of K)).obj (Over.mk ((V t).f j ≫ source.hom))).unop) ∧
        Function.Injective (affineCoverSectionMap q (V t)) ∧
        ∀ j, ((V t).f j ≫ q.left) ≫ (W t).ι =
          (V t).f j ≫ (f.left ⁻¹ᵁ W t).ι ≫ f.left := by
  let (t : T) : IsAffine (W t).toScheme := hW t
  let (t : T) : CompactSpace (f.left ⁻¹ᵁ W t).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f.left ∣_ W t)
  let V (t : T) := (f.left ⁻¹ᵁ W t).toScheme.affineCover.finiteSubcover
  have hV (t : T) (j : (V t).I₀) : IsAffine ((V t).X j) := by
    change IsAffine ((f.left ⁻¹ᵁ W t).toScheme.affineCover.X _)
    infer_instance
  refine ⟨V, inferInstance, hcover, (fun _ ↦ inferInstance), hV, ?_⟩
  intro t
  let target := Over.mk ((W t).ι ≫ Y.hom)
  let source := Over.mk ((f.left ∣_ W t) ≫ target.hom)
  let q : source ⟶ target := Over.homMk (f.left ∣_ W t) rfl
  let : LocallyOfFiniteType target.hom := by
    change LocallyOfFiniteType ((W t).ι ≫ Y.hom)
    infer_instance
  let : LocallyOfFiniteType source.hom := by
    change LocallyOfFiniteType ((f.left ∣_ W t) ≫ target.hom)
    infer_instance
  let (j : (V t).I₀) : IsAffine ((V t).X j) := hV t j
  have hfinite (j : (V t).I₀) : Algebra.FiniteType K
      ((algΓ (.of K)).obj (Over.mk ((V t).f j ≫ source.hom))).unop := by
    have hloc : LocallyOfFiniteType
        (Over.mk ((V t).f j ≫ source.hom)).hom := by
      change LocallyOfFiniteType ((V t).f j ≫ source.hom)
      infer_instance
    exact @coordinates_finiteType K _ (Over.mk ((V t).f j ≫ source.hom)) (hV t j) hloc
  let := hfinite
  have htarget : Algebra.FiniteType K ((algΓ (.of K)).obj target).unop :=
    @coordinates_finiteType K _ target (hW t) inferInstance
  have hqc : QuasiCompact q.left := by
    change QuasiCompact (f.left ∣_ W t)
    infer_instance
  have hsurj : Surjective q.left := by
    change Surjective (f.left ∣_ W t)
    exact MorphismProperty.of_isPullback
      (isPullback_morphismRestrict f.left (W t)).flip (inferInstance : Surjective f.left)
  have hreduced : IsReduced target.left := by
    change IsReduced (W t).toScheme
    infer_instance
  have hinj := @affineCoverSectionMap_injective K _ source target q (V t) hqc hsurj hreduced
  refine ⟨htarget, hfinite, finiteType_pi K (V t).I₀ _, hinj, ?_⟩
  intro j
  change ((V t).f j ≫ (f.left ∣_ W t)) ≫ (W t).ι = _
  rw [Category.assoc, morphismRestrict_ι]

end
end SchubertGeometry

namespace SchubertGeometry

noncomputable section

open ReductiveGroups GroupActions FrobeniusSplitting

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)

private instance pairedEndpoint_surjective :
    Surjective (pairedRichardsonMap G a b ha hb).left := by
  let := pairedRichardsonMap_geomConnected G a b ha hb
  infer_instance

private instance pairedTarget_reduced :
    IsReduced (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toOver.left := by
  change IsReduced (richardsonVariety G
    (G.longestElement * simpleWeylWord G.rootBase b)
    (simpleWeylWord G.rootBase a)).scheme
  exact (richardsonVariety G _ _).reduced

private instance pairedTarget_finiteType :
    LocallyOfFiniteType (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toOver.hom := by
  change LocallyOfFiniteType (richardsonVariety G
    (G.longestElement * simpleWeylWord G.rootBase b)
    (simpleWeylWord G.rootBase a)).toSpec
  exact (richardsonVariety G _ _).locallyOfFiniteType

private theorem targetPatches_affine {T : Type u}
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t)) (t : T) :
    IsAffineOpen ((richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ⁻¹ᵁ U t) :=
  (hU t).preimage _

private theorem targetPatches_cover {T : Type u}
    (U : T → (flagVariety G).scheme.Opens) (hcover : (⨆ t, U t) = ⊤) :
    (⨆ t, (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ⁻¹ᵁ U t) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ hcover

include G a b ha hb

end
end SchubertGeometry
