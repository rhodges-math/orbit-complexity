import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Detecting module isomorphisms on open ranges -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

private theorem restrictIso_reflects {X Y : Scheme.{u}} (e : X ≅ Y)
    {M N : Y.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor e.hom).map a)] : IsIso a := by
  let F := restrictFunctor e.hom
  let G := restrictFunctor e.inv
  let η : F ⋙ G ≅ 𝟭 Y.Modules :=
    (restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr e.inv_hom_id ≪≫ restrictFunctorId
  have ht : IsIso ((F ⋙ G).map a) := by
    change IsIso (G.map ((restrictFunctor e.hom).map a))
    infer_instance
  exact (NatIso.isIso_map_iff η a).mp ht

/-- An isomorphism after an open chart is an isomorphism over its open range. -/
theorem isIso_over_of_restrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor j).map a)] : IsIso (a.over j.opensRange) := by
  let U := j.opensRange
  let e := j.isoOpensRange
  let τ : restrictFunctor j ≅ restrictFunctor U.ι ⋙ restrictFunctor e.hom :=
    restrictFunctorCongr j.isoOpensRange_hom_ι.symm ≪≫ restrictFunctorComp e.hom U.ι
  have ht : IsIso ((restrictFunctor e.hom).map ((restrictFunctor U.ι).map a)) :=
    (NatIso.isIso_map_iff τ a).mp inferInstance
  let : IsIso ((restrictFunctor e.hom).map ((restrictFunctor U.ι).map a)) := ht
  have hu : IsIso ((restrictFunctor U.ι).map a) := restrictIso_reflects e _
  have he : IsIso ((overEquiv U).functor.map (a.over U)) :=
    (NatIso.isIso_map_iff (overFunctorEquiv U) a).mpr hu
  let : IsIso ((overEquiv U).functor.map (a.over U)) := he
  exact isIso_of_reflects_iso (a.over U) (overEquiv U).functor

end FrobeniusSplitting.OperatorSheaf
