import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing module-sheaf morphisms on open families -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u v

namespace FrobeniusSplitting.OperatorSheaf

/-- Compatible local module morphisms glue to a morphism of the original sheaves. -/
theorem glueModuleMorphisms {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (hcover : iSup U = ⊤) (M N : X.Modules)
    (k : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hcompatible : TopCat.Presheaf.IsCompatible (SheafOfModules.linearHom M N).obj U
      (fun i => (SheafOfModules.linearHomObjEquiv M N (U i)).symm (k i))) :
    ∃ f : M ⟶ N, ∀ i, f.over (U i) = k i := by
  let H := SheafOfModules.linearHom M N
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing' (X := X.toTopCat) H U ⊤ (fun i => (U
      i).leTop)
    hcover.ge (fun i => (SheafOfModules.linearHomObjEquiv M N (U i)).symm (k i))
    hcompatible
  let s : H.obj.sections :=
    { val V := H.obj.map V.unop.leTop.op t
      property {V W} g := by
        exact congrArg (fun a : H.obj.obj (op ⊤) ⟶ H.obj.obj W => a t)
          (H.obj.map_comp V.unop.leTop.op g).symm }
  let f := SheafOfModules.linearHomSectionsEquiv M N s
  refine ⟨f, ?_⟩
  intro i
  have hs := congrArg (fun a : H.obj.sections => a.val (op (U i)))
    ((SheafOfModules.linearHomSectionsEquiv M N).symm_apply_apply s)
  have hf : (SheafOfModules.linearHomObjEquiv M N (U i)).symm (f.over (U i)) =
      (SheafOfModules.linearHomObjEquiv M N (U i)).symm (k i) := hs.trans (ht i)
  exact (SheafOfModules.linearHomObjEquiv M N (U i)).symm.injective hf

/-- A local section gives its scalar-multiplication morphism on the restricted sheaf. -/
def localSectionHom {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (s : N.val.obj (op U)) :
    (SheafOfModules.unit X.ringCatSheaf).over U ⟶ N.over U :=
  (N.over U).unitHomEquiv.symm
    { val V := (N.val.map V.unop.hom.op).hom s
      property {V W} f := by
        change (N.val.map f.unop.left.op).hom ((N.val.map V.unop.hom.op).hom s) =
          (N.val.map W.unop.hom.op).hom s
        exact (N.val.map_comp_apply V.unop.hom.op f.unop.left.op s).symm }

/-- The local section morphism multiplies its restricted section by the input scalar. -/
theorem localSectionHom_apply {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (s : N.val.obj (op U)) (V : Over U) (r : Γ(X, V.left)) :
    ((localSectionHom N U s).val.app (op V)).hom r =
      (N.smul r).hom ((N.val.map V.hom.op).hom s) := rfl

private theorem isIsoOfComponents {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (t : M ⟶ N)
    (h : ∀ V, IsIso (t.val.app V)) : IsIso t := by
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun V => @asIso _ _ _ _ (t.val.app V) (h V)) (fun {_ _} f => t.val.naturality f)
  have he : e.hom = t.val := by ext V; rfl
  let q : M ≅ N := (SheafOfModules.fullyFaithfulForget R).preimageIso e
  have hq : q.hom = t :=
    (SheafOfModules.fullyFaithfulForget R).map_injective (X := M) (Y := N)
      (((SheafOfModules.fullyFaithfulForget R).map_preimage (X := M) (Y := N) e.hom).trans he)
  exact hq ▸ q.isIso_hom

private def unitMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The unit restriction map is invertible over the range of an open immersion. -/
def unitOverRangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (SheafOfModules.unit Y.ringCatSheaf).over f.opensRange ≅
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).over f.opensRange :=
  @asIso _ _ _ _ ((unitMap f).over f.opensRange) (by
    apply isIsoOfComponents
    intro V
    have hf : IsIso (f.app V.unop.left) :=
      f.isIso_app V.unop.left (leOfHom V.unop.hom)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (f.app V.unop.left)
    exact (ConcreteCategory.isIso_iff_bijective (f.app V.unop.left)).mp hf)

/-- The range isomorphism has the structure-sheaf map as its forward components. -/
theorem unitOverRangeIso_hom_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (V : Over f.opensRange) (r : Γ(Y, V.left)) :
    (((unitOverRangeIso f).hom.val.app (op V)).hom r) = f.app V.left r := rfl

end FrobeniusSplitting.OperatorSheaf
