import OrbitComplexity.FrobeniusSplitting.Normality.Limits.CoefficientLimit
import OrbitComplexity.SchubertGeometry.Parabolics.BruhatClosure
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Data.Finset.Order

/-! # Weyl sections of the same closed Schubert models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u v

private theorem coefficientSpec_comp {K : Type u} [CommRing K]
    {R T : Subalgebra ℤ K} (hRT : R ≤ T) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      Spec.map (CommRingCat.ofHom (algebraMap T K)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) := by
  let f : CommRingCat.of R ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom
  let g : CommRingCat.of T ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (algebraMap T K)
  have hfg : f ≫ g = CommRingCat.ofHom (algebraMap R K) := by
    ext x
    rfl
  exact (congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of K => Spec.map k) hfg).symm.trans
    (Spec.map_comp f g)

private theorem coefficientStage_comp {K : Type u} [CommRing K]
    {S R T : Subalgebra ℤ K} (hSR : S ≤ R) (hRT : R ≤ T) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hSR.trans hRT)).toRingHom) :=
  (Spec.map_comp
    (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom)
    (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)).symm

private theorem retainPoint {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of S)) [LocallyOfFinitePresentation a]
    (z : Spec (.of K) ⟶ Y)
    (hz : z ≫ a = Spec.map (CommRingCat.ofHom (algebraMap S K))) :
    ∃ (r : CoefficientStage S) (b : Spec (.of r.val) ⟶ Y),
      b ≫ a = Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion r.property.2).toRingHom) ∧
      z = Spec.map (CommRingCat.ofHom (algebraMap r.val K)) ≫ b := by
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  let t : coefficientSchemes S ⟶ (Functor.const _).obj (Spec (.of S)) :=
    { app := fun j => Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion j.unop.property.2).toRingHom)
      naturality := fun j k f => by
        change (coefficientSchemes S).map f ≫ _ = _ ≫ 𝟙 _
        exact (Spec.map_comp
          (CommRingCat.ofHom (Subalgebra.inclusion k.unop.property.2).toRingHom)
          ((coefficientRings S).map f.unop)).symm.trans (Category.comp_id _).symm }
  have hbase : (coefficientSpecCone S).π ≫ t = (Functor.const _).map (z ≫ a) := by
    ext j
    change Spec.map (CommRingCat.ofHom (algebraMap j.unop.val K)) ≫
      Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion j.unop.property.2).toRingHom) = z ≫ a
    exact (Spec.map_comp
      (CommRingCat.ofHom (Subalgebra.inclusion j.unop.property.2).toRingHom)
      (CommRingCat.ofHom (algebraMap j.unop.val K))).symm.trans hz.symm
  let : ∀ {j k : (CoefficientStage S)ᵒᵖ} (f : j ⟶ k),
      IsAffineHom ((coefficientSchemes S).map f) := fun f => by
    change IsAffineHom (Spec.map _)
    infer_instance
  let : ∀ j, CompactSpace ((coefficientSchemes S).obj j) := fun j => by
    change CompactSpace (Spec _)
    infer_instance
  let : ∀ j, QuasiSeparatedSpace ((coefficientSchemes S).obj j) := fun j => by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  obtain ⟨r, b, hb, ha⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (coefficientSchemes S) t a (coefficientSpecCone S) (coefficientSpecLimit S hS) z hbase
  exact ⟨r.unop, b, ha, hb.symm⟩

/-- All selected lower Weyl points give sections of the same chosen
Schubert models on one coefficient stage. Their flag images and original
generic comparison triangles are retained. -/
theorem exists_schubert_weyl_sections
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    {J : Type v} [Finite J] (w v : J → G.weylGroup)
    (hwv : ∀ j, WeylBruhatLE G.rootBase (w j) (v j))
    (Y : J → Over (Spec (.of S))) [∀ j, LocallyOfFinitePresentation (Y j).hom]
    (qY : ∀ j, (schubertVariety G (v j)).scheme ⟶ (Y j).left)
    (hY : ∀ j, qY j ≫ (Y j).hom = (schubertVariety G (v j)).toSpec ≫
      Spec.map (CommRingCat.ofHom (algebraMap S K))) :
    ∃ (r : CoefficientStage S) (p : ∀ j, (schubertVariety G (v j)).points)
      (b : ∀ j, Spec (.of r.val) ⟶ (Y j).left),
      (∀ j, (p j).val ≫ (schubertInclusion G (v j)).left = (weylFlagPoint G (w j)).val) ∧
      (∀ j, b j ≫ (Y j).hom = Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion r.property.2).toRingHom)) ∧
      ∀ j, (p j).val ≫ qY j =
        Spec.map (CommRingCat.ofHom (algebraMap r.val K)) ≫ b j := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  choose p hp using fun j => (weylFlag_mem_schubert_iff G (w j) (v j)).mpr (hwv j)
  have hpoint (j : J) : (p j).val ≫ (schubertInclusion G (v j)).left =
      (weylFlagPoint G (w j)).val := congrArg Subtype.val (hp j)
  have hz (j : J) : ((p j).val ≫ qY j) ≫ (Y j).hom =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
    calc
      _ = (p j).val ≫ ((schubertVariety G (v j)).toSpec ≫ _) :=
        (Category.assoc _ _ _).trans (congrArg (fun z => (p j).val ≫ z) (hY j))
      _ = ((p j).val ≫ (schubertVariety G (v j)).toSpec) ≫ _ :=
        (Category.assoc _ _ _).symm
      _ = _ := (congrArg (fun z => z ≫ _) (p j).property).trans (Category.id_comp _)
  choose r b hb hn using fun j => retainPoint S hS (Y j).hom ((p j).val ≫ qY j) (hz j)
  obtain ⟨s, hs⟩ := Finset.exists_le (Finset.univ.image r)
  have hrs j : r j ≤ s := hs (r j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  let ρ j := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hrs j)).toRingHom)
  refine ⟨s, p, fun j => ρ j ≫ b j, hpoint, ?_, ?_⟩
  · intro j
    calc
      (ρ j ≫ b j) ≫ (Y j).hom = ρ j ≫ Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (r j).property.2).toRingHom) :=
        (Category.assoc _ _ _).trans (congrArg (fun z => ρ j ≫ z) (hb j))
      _ = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion s.property.2).toRingHom) :=
        coefficientStage_comp (r j).property.2 (hrs j)
  · intro j
    calc
      (p j).val ≫ qY j = Spec.map (CommRingCat.ofHom (algebraMap (r j).val K)) ≫ b j :=
        hn j
      _ = (Spec.map (CommRingCat.ofHom (algebraMap s.val K)) ≫ ρ j) ≫ b j :=
        congrArg (fun z => z ≫ b j) (coefficientSpec_comp (hrs j))
      _ = Spec.map (CommRingCat.ofHom (algebraMap s.val K)) ≫ (ρ j ≫ b j) :=
        Category.assoc _ _ _


end SchubertGeometry
