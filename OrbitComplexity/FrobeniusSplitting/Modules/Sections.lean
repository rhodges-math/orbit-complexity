import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.Stalks

/-! # Sections and restrictions of module sheaves -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace FrobeniusSplitting
universe u

open CategoryTheory.Functor

/-- Restriction to an open subscheme preserves finite limits of module sheaves. -/
instance restriction_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let e : Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X ≅
      Scheme.Modules.toPresheaf Y ⋙
        (whiskeringLeft _ _ _).obj f.opensFunctor.op :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  let : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
  let : PreservesFiniteLimits ((whiskeringLeft (X.Opens)ᵒᵖ (Y.Opens)ᵒᵖ
      AddCommGrpCat.{u}).obj f.opensFunctor.op) := inferInstance
  let : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf X)

/-- On an open chart whose preimage lies in an open subscheme, restriction of the
structure-sheaf comparison is an isomorphism. -/
theorem restriction_unit_isIso {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : W ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion i]
    (h : ∀ U : X.Opens, g ⁻¹ᵁ (f ''ᵁ U) ≤ i.opensRange) :
    IsIso ((Scheme.Modules.restrictFunctor f).map
      ((Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))) := by
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app (X := X)).mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective ((i.app (g ⁻¹ᵁ (f ''ᵁ U))).hom)
  let := Scheme.Hom.isIso_app i (g ⁻¹ᵁ (f ''ᵁ U)) (h U)
  exact ConcreteCategory.bijective_of_isIso _

private abbrev evaluate (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules X.ringCatSheaf ⥤ ModuleCat Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (.op U)

private def sectionsCocone (X : Scheme.{u}) (U : X.Opens) (I : Type u) :
    Cofan (fun _ : I => ModuleCat.of Γ(X, U) Γ(X, U)) :=
  Cofan.mk ((evaluate X U).obj (SheafOfModules.free I))
    (fun i => (evaluate X U).map (SheafOfModules.ιFree i))

private def sectionsCocone_colimit (X : Scheme.{u}) (U : X.Opens) (I : Type u)
    [Finite I] : IsColimit (sectionsCocone X U I) := by
  let E := evaluate X U
  let : E.Additive :=
    { map_add := by intro M N f g; rfl }
  let : PreservesColimitsOfShape (Discrete I) E := inferInstance
  let e : (Discrete.functor (fun _ : I => SheafOfModules.unit X.ringCatSheaf)) ⋙ E ≅
      Discrete.functor (fun _ : I => ModuleCat.of Γ(X, U) Γ(X, U)) :=
    Discrete.natIso (fun _ => Iso.refl _)
  have h := (IsColimit.precomposeHomEquiv e.symm _).symm
    (isColimitOfPreserves E (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I))
  refine IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _) ?_)
  rintro ⟨i⟩
  ext
  rfl

/-- On each open, the sections of a finite free module sheaf have the ordinary
finitely supported coordinates over the ring of functions on that open. -/
def finiteFreeSectionsIso (X : Scheme.{u}) (U : X.Opens) (I : Type u) [Finite I] :
    ModuleCat.of Γ(X, U) (I →₀ Γ(X, U)) ≅
      (SheafOfModules.evaluation X.ringCatSheaf (.op U)).obj (SheafOfModules.free I) :=
  (ModuleCat.finsuppCoconeIsColimit Γ(X, U) Γ(X, U) I).coconePointUniqueUpToIso
    (sectionsCocone_colimit X U I)

/-- A coordinate vector is the indicated free generator with the indicated coefficient. -/
theorem finiteFreeSectionsIso_single (X : Scheme.{u}) (U : X.Opens) (I : Type u)
    [Finite I] (i : I) (r : Γ(X, U)) :
    (finiteFreeSectionsIso X U I).hom.hom (Finsupp.single i r) =
      ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (.op U)).hom r := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit Γ(X, U) Γ(X, U) I)
    (sectionsCocone_colimit X U I) (Discrete.mk i)
  exact congrArg (fun f => ModuleCat.Hom.hom f r) h

/-- A morphism of quasicoherent modules on an affine scheme is an isomorphism
when its map on global sections is bijective. -/
theorem affineModule_isIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (h : Function.Bijective ((moduleSpecΓFunctor (R := R)).map f).hom) : IsIso f := by
  let : IsIso ((moduleSpecΓFunctor (R := R)).map f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  have he := Scheme.Modules.fromTildeΓNatTrans.naturality f
  change (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f) ≫
    N.fromTildeΓ = M.fromTildeΓ ≫ f at he
  have : IsIso (M.fromTildeΓ ≫ f) := by
    rw [← he]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N)
  exact IsIso.of_isIso_comp_left M.fromTildeΓ f

/-- A module-sheaf morphism is an isomorphism if its restrictions to an open cover are. -/
theorem isIso_on_open_family {X : Scheme.{u}} {I : Type u}
    (A : I → Scheme.{u}) (f : ∀ i, A i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ (i : I) (y : A i), f i y = x)
    {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (f i)).map φ)) : IsIso φ := by
  have hs (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map φ)) := by
    obtain ⟨i, y, rfl⟩ := hcover x
    let e := Scheme.Modules.restrictStalkNatIso (f i) y
    let : IsIso ((Scheme.Modules.restrictFunctor (f i)).map φ) := h i
    have hi : IsIso ((Scheme.Modules.restrictFunctor (f i) ⋙
        Scheme.Modules.toPresheaf (A i) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) := by
      change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((Scheme.Modules.toPresheaf (A i)).map
          ((Scheme.Modules.restrictFunctor (f i)).map φ)))
      infer_instance
    let : IsIso ((Scheme.Modules.restrictFunctor (f i) ⋙
        Scheme.Modules.toPresheaf (A i) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) := hi
    have hn := e.hom.naturality φ
    have hc : IsIso (e.hom.app M ≫
        (Scheme.Modules.toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f i y)).map φ) := by
      rw [← hn]
      infer_instance
    let : IsIso (e.hom.app M ≫ (Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f i y)).map φ) := hc
    exact IsIso.of_isIso_comp_left (e.hom.app M)
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f i y)).map φ)
  let s := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hi : IsIso s := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso s).mpr hs
  have hp : IsIso ((Scheme.Modules.toPresheaf X).map φ) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) s hi
  let : IsIso ((Scheme.Modules.toPresheaf X).map φ) := hp
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

end FrobeniusSplitting
