import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFamilySections
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalDetection
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Reflecting a coframed section through flat scalar extension

An injective coefficient extension remains schematically dominant after flat
base change. Its injective map on global functions reflects the coefficient of
a section in a coframe, including on nonaffine schemes.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace SchubertGeometry.RetainedCharacter

open private SchubertGeometry.ProjectiveLine.spec_dominant from
  OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalDetection
open private section_reflection from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFamilySections
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem scalar_injective {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hi : Function.Injective (algebraMap R K))
    {X XK : Scheme.{u}} (base : X ⟶ Spec (.of R)) [Flat base]
    (baseK : XK ⟶ Spec (.of K)) (q : XK ⟶ X)
    (hq : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    Function.Injective q.appTop.hom := by
  let : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    SchubertGeometry.ProjectiveLine.spec_dominant (algebraMap R K) hi
  let : IsSchemeTheoreticallyDominant q :=
    IsSchemeTheoreticallyDominant.of_isPullback hq.flip
  let : QuasiCompact q := MorphismProperty.of_isPullback hq.flip inferInstance
  exact q.app_injective ⊤

/-- A section coefficient in a fixed coframe descends through injective flat
scalar extension when its coefficient on the compared fibre is the scalar image. -/
theorem flatSection_reflect {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hi : Function.Injective (algebraMap R K))
    {X XK : Scheme.{u}} (base : X ⟶ Spec (.of R)) [Flat base]
    (baseK : XK ⟶ Spec (.of K)) (q : XK ⟶ X)
    (hq : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (L : X.Modules) (s : unitModule X ⟶ L) (F : L ≅ unitModule X)
    (FK : (Scheme.Modules.pullback q).obj L ≅ unitModule XK)
    (hF : (Scheme.Modules.pullback q).mapIso F ≪≫
      Scheme.Modules.pullbackObjUnitIso q = FK)
    (c : Γ(X, ⊤)) (r : Γ(XK, ⊤)) (hr : q.appTop.hom c = r)
    (h : pullSection q L s ≫ FK.hom =
      Scheme.Modules.globalSectionsSmul (unitModule XK) r) :
    s ≫ F.hom = Scheme.Modules.globalSectionsSmul (unitModule X) c := by
  apply section_reflection q (scalar_injective hi base baseK q hq) L s F c
  exact (congrArg (fun E : (Scheme.Modules.pullback q).obj L ≅ unitModule XK =>
    pullSection q L s ≫ E.hom) hF).trans
      (h.trans (congrArg (Scheme.Modules.globalSectionsSmul (unitModule XK)) hr.symm))

end SchubertGeometry.RetainedCharacter
