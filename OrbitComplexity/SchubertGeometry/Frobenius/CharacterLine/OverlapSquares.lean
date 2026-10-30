import OrbitComplexity.SchubertGeometry.Normality.Transitions.RetainedPriorCharts

/-! # intersections in the same retained affine cocone -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u v w
namespace SchubertGeometry.RetainedCharacter

/-- The union node is the specified common restriction, before taking any colimit. -/
def unionIndex {J : Type u} (s t : {s : Finset J // s.Nonempty}) :
    {s : Finset J // s.Nonempty} := by
  classical
  exact ⟨s.val ∪ t.val, s.property.mono Finset.subset_union_left⟩

/-- The first original restriction into the union node. -/
def unionLeft {J : Type u} (s t : {s : Finset J // s.Nonempty}) :
    s ⟶ unionIndex s t := by
  classical
  exact homOfLE Finset.subset_union_left

/-- The second original restriction into the union node. -/
def unionRight {J : Type u} (s t : {s : Finset J // s.Nonempty}) :
    t ⟶ unionIndex s t := by
  classical
  exact homOfLE Finset.subset_union_right

private theorem common_refinement {I : Type v} [Category.{w} I]
    [Quiver.IsThin I] [Small.{u} I] (E : I ⥤ Scheme.{u})
    [∀ {a b} (f : a ⟶ b), IsOpenImmersion (E.map f)]
    [(E ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone E) (hc : IsColimit c) {a b : I}
    (x : E.obj a) (y : E.obj b) (h : c.ι.app a x = c.ι.app b y) :
    ∃ k, ∃ (f : k ⟶ a) (g : k ⟶ b) (z : E.obj k),
      E.map f z = x ∧ E.map g z = y := by
  let e : colimit E ≅ c.pt := (colimit.isColimit E).coconePointUniqueUpToIso hc
  have hcol : colimit.ι E a x = colimit.ι E b y := by
    apply e.hom.isOpenEmbedding.injective
    have ha : colimit.ι E a ≫ e.hom = c.ι.app a :=
      (colimit.isColimit E).comp_coconePointUniqueUpToIso_hom hc a
    have hb : colimit.ι E b ≫ e.hom = c.ι.app b :=
      (colimit.isColimit E).comp_coconePointUniqueUpToIso_hom hc b
    have hp := (congrArg (fun f ↦ f x) ha).trans
      (h.trans (congrArg (fun f ↦ f y) hb).symm)
    simpa only [Scheme.Hom.comp_apply] using hp
  exact (Scheme.IsLocallyDirected.ι_eq_ι_iff E).mp hcol

/-- The original union restrictions form the Cartesian overlap square
in the chosen cocone. No new affine cover is selected. -/
theorem retained_overlap_square {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hmapOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdirected : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (s t : {s : Finset J // s.Nonempty}) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (N.map (unionLeft s t)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (N.map (unionRight s t)).hom.toRingHom))
      (cG.ι.app (.op s)).left (cG.ι.app (.op t)).left := by
  classical
  let E := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let eOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (E.map f) := by
    intro s t f
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom))
    exact hmapOpen f.unop
  let : ∀ {a b : {s : Finset J // s.Nonempty}ᵒᵖ} (f : a ⟶ b),
      IsOpenImmersion (E.map f) := @eOpen
  let : (E ⋙ Scheme.forget).IsLocallyDirected := hdirected
  let C : Cocone E := (Over.forget (Spec (.of R))).mapCocone cG
  let hC : IsColimit C := isColimitOfPreserves (Over.forget (Spec (.of R))) hcG
  obtain ⟨hopen, hleg, _⟩ := retained_prior_charts N cG hcG
  let l := Spec.map (CommRingCat.ofHom (N.map (unionLeft s t)).hom.toRingHom)
  let r := Spec.map (CommRingCat.ofHom (N.map (unionRight s t)).hom.toRingHom)
  have H : r ≫ (cG.ι.app (.op t)).left = l ≫ (cG.ι.app (.op s)).left :=
    (hleg _ _ (unionRight s t)).trans (hleg _ _ (unionLeft s t)).symm
  refine @IsOpenImmersion.isPullback _ _ _ _ l r
    (cG.ι.app (.op s)).left (cG.ι.app (.op t)).left
    (hmapOpen (unionRight s t)) (hopen s) H ?_
  ext x
  change (∃ y, (cG.ι.app (.op s)).left y = (cG.ι.app (.op t)).left x) ↔
    ∃ z, r z = x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, f, g, z, hz⟩ := common_refinement E C hC y x hy
    have hu : (unionIndex s t).val ⊆ k.unop.val := by
      change s.val ∪ t.val ⊆ k.unop.val
      exact Finset.union_subset (leOfHom f.unop) (leOfHom g.unop)
    let h : unionIndex s t ⟶ k.unop := homOfLE hu
    refine ⟨E.map h.op z, ?_⟩
    change E.map (unionRight s t).op (E.map h.op z) = x
    rw [← Scheme.Hom.comp_apply, ← E.map_comp]
    have hh : h.op ≫ (unionRight s t).op = g := Subsingleton.elim _ _
    rw [hh]
    exact hz.2
  · rintro ⟨z, rfl⟩
    refine ⟨l z, ?_⟩
    have hp : (l ≫ (cG.ι.app (.op s)).left) z =
        (r ≫ (cG.ι.app (.op t)).left) z :=
      congrArg (fun f : Spec (.of (N.obj (unionIndex s t))) ⟶ cG.pt.left ↦ f z) H.symm
    exact (Scheme.Hom.comp_apply l (cG.ι.app (.op s)).left z).symm.trans
      (hp.trans (Scheme.Hom.comp_apply r (cG.ι.app (.op t)).left z))

end SchubertGeometry.RetainedCharacter
