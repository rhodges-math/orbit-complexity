import OrbitComplexity.GroupActions.Rosenlicht.OrbitMorphism
import OrbitComplexity.GroupActions.Rosenlicht.SurjectiveRestriction
import OrbitComplexity.GroupActions.Rosenlicht.InvariantPreimages
import OrbitComplexity.GroupActions.Rosenlicht.DomainLifts

/-!
# Surjective morphisms with orbit fibres

Restriction over an open subset of the invariant model gives a surjective morphism from a
nonempty stable open subvariety whose rational-point fibres are the group orbits.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A nonempty invariant open subvariety admits a surjective morphism whose
rational-point fibres are the group orbits and which factors the invariant map. -/
theorem exists_surjective_orbit_morphism :
    ∃ V : (invariantModel H X).scheme.Opens,
      (V : Set (invariantModel H X).scheme).Nonempty ∧
      ∃ Z : GroupActions.Variety K, Nonempty Z.scheme ∧ IrreducibleSpace Z.scheme ∧
        ∃ M : ModObj H.toOver Z.toOver,
          letI := M
          ∃ i : Z.toOver ⟶ X.toOver, IsOpenImmersion i.left ∧ IsDominant i.left ∧
            IsModHom H.toOver i ∧
            ∃ d : Z.toOver ⟶ (invariantDomain H X).toOver, IsDominant d.left ∧
              d ≫ X.openInclusion (invariantMap H X).domain = i ∧
              ∃ q : Z.toOver ⟶ ((invariantModel H X).openSubvariety V).toOver,
                Surjective q.left ∧
                q ≫ (invariantModel H X).openInclusion V = d ≫ invariantMorphism H X ∧
                ∀ x y : Z.points, mapPoints q x = mapPoints q y ↔
                  y ∈ MulAction.orbit H.points x := by
  obtain ⟨U, hU, hUD, hF⟩ := exists_saturated_orbit_morphism H X
  let s := saturationOpen H X U
  let S := X.openSubvariety s
  have hs : (s : Set X.scheme).Nonempty := saturationOpen_nonempty H X U hU
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsOpenImmersion s.ι := X.openInclusion_isOpenImmersion s
  have : IsIntegral s.toScheme := isIntegral_of_isOpenImmersion s.ι
  have : IsIntegral S.scheme := inferInstanceAs (IsIntegral s.toScheme)
  let : ModObj H.toOver S.toOver := saturationAction H X U
  let f : S.toOver ⟶ (invariantModel H X).toOver := invariantMorphismOn H X s hUD
  have : IsDominant f.left := invariantMorphismOn_dominant H X s hUD
  have hf : ∀ (g : H.points) (x : S.points), mapPoints f (g • x) = mapPoints f x := by
    intro g x
    exact ((hF x (g • x)).mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)).symm
  obtain ⟨V, hV, hsurj⟩ := exists_surjective_restrict f
  let T := f.left ⁻¹ᵁ V
  let Z := S.openSubvariety T
  let M : ModObj H.toOver Z.toOver := invariantPreimageAction H f hf V
  let : ModObj H.toOver Z.toOver := M
  let iZ : Z.toOver ⟶ S.toOver := S.openInclusion T
  let iS : S.toOver ⟶ X.toOver := X.openInclusion s
  let i : Z.toOver ⟶ X.toOver := iZ ≫ iS
  let dS : S.toOver ⟶ (invariantDomain H X).toOver := invariantDomainLift H X s hUD
  let d : Z.toOver ⟶ (invariantDomain H X).toOver := iZ ≫ dS
  let q : Z.toOver ⟶ ((invariantModel H X).openSubvariety V).toOver := restrictHom f V
  have : Surjective q.left := hsurj
  have hZne : Nonempty Z.scheme := by
    have : Nonempty ((invariantModel H X).openSubvariety V).scheme :=
      Set.nonempty_coe_sort.mpr hV
    obtain ⟨y⟩ := (inferInstance : Nonempty ((invariantModel H X).openSubvariety V).scheme)
    obtain ⟨z, -⟩ := q.left.surjective y
    exact ⟨z⟩
  have : Nonempty Z.scheme := hZne
  have : IsOpenImmersion iZ.left := S.openInclusion_isOpenImmersion T
  have : IsOpenImmersion iS.left := X.openInclusion_isOpenImmersion s
  have hiOpen : IsOpenImmersion i.left := by
    change IsOpenImmersion (iZ.left ≫ iS.left)
    infer_instance
  let ix : Z.scheme ⟶ X.scheme := i.left
  have : IsOpenImmersion ix := hiOpen
  have hZirr : IrreducibleSpace Z.scheme := ix.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace Z.scheme := hZirr
  have hiDom : IsDominant i.left := by
    change IsDominant ix
    exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace ix ix.isOpenEmbedding.isOpenMap⟩
  have : IsModHom H.toOver iZ := invariantPreimage_isModHom H f hf V
  have : IsModHom H.toOver iS := saturationInclusion_isModHom H X U
  have hiMod : IsModHom H.toOver i := by
    change IsModHom H.toOver (iZ ≫ iS)
    infer_instance
  have : IsDominant iZ.left := by
    let iz : Z.scheme ⟶ S.scheme := iZ.left
    have : IsOpenImmersion iz := inferInstanceAs (IsOpenImmersion iZ.left)
    change IsDominant iz
    exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace iz iz.isOpenEmbedding.isOpenMap⟩
  have : IsDominant dS.left := invariantDomainLift_dominant H X s hUD
  have hdDom : IsDominant d.left := by
    change IsDominant (iZ.left ≫ dS.left)
    infer_instance
  have hdi : d ≫ X.openInclusion (invariantMap H X).domain = i := by
    calc
      _ = iZ ≫ (dS ≫ X.openInclusion (invariantMap H X).domain) := Category.assoc _ _ _
      _ = iZ ≫ iS := congrArg (fun k ↦ iZ ≫ k) (invariantDomainLift_inclusion H X s hUD)
      _ = i := rfl
  have hqd : q ≫ (invariantModel H X).openInclusion V = d ≫ invariantMorphism H X := by
    calc
      _ = iZ ≫ f := restrictHom_comp_inclusion f V
      _ = iZ ≫ (dS ≫ invariantMorphism H X) :=
        congrArg (fun k ↦ iZ ≫ k) (invariantDomainLift_morphism H X s hUD).symm
      _ = d ≫ invariantMorphism H X := (Category.assoc _ _ _).symm
  have hquot (x y : Z.points) : mapPoints q x = mapPoints q y ↔
      y ∈ MulAction.orbit H.points x := by
    constructor
    · intro he
      have hS := (hF (mapPoints iZ x) (mapPoints iZ y)).mp
        ((restrictHom_fibres f V x y).mp he)
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hS
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g, ?_⟩
      apply mapPoints_injective_of_mono iZ
      exact (invariantPreimage_smul H f hf V g x).trans hg
    · intro he
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp he
      apply (restrictHom_fibres f V x (g • x)).mpr
      apply (hF (mapPoints iZ x) (mapPoints iZ (g • x))).mpr
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨g, (invariantPreimage_smul H f hf V g x).symm⟩
  exact ⟨V, hV, Z, hZne, hZirr, M, i, hiOpen, hiDom, hiMod,
    d, hdDom, hdi, q, hsurj, hqd, hquot⟩

end

end GroupActions.Variety
