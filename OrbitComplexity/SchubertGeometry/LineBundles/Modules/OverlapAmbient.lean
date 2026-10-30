import OrbitComplexity.SchubertGeometry.LineBundles.Modules.OverlapCoordinate

/-! # The ambient group coordinate of the rank-one Borel overlap -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev coordinate (K : Type u) [Field K] :=
  MonoidAlgebra K (Multiplicative ℤ)

/-- The regular Borel overlap includes as the fixed coroot-times-root factor in G. -/
theorem simpleOverlapCoordinate_ambient (i : G.rootBase.support) :
    (simpleOverlapCoordinate G i).comp
      (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom.toAlgHom =
      (toConv (Coroot.simpleCorootMap G i).toAlgHom *
        gaParameterPoint (G.simpleRootMap i)
          (-MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1 : coordinate K)).ofConv := by
  let q : G.coordinateAlgebra →ₐc[K] G.borelAlgebra :=
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom
  let t : WithConv (G.borelAlgebra →ₐ[K] coordinate K) :=
    toConv ((((MonoidAlgebra.mapDomainBialgHom K
      (Coroot.simpleCorootCharacter G i)).comp (torusCharacterCoordinates G)).toAlgHom).comp
        (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
          G.borel_le_torus).hom.toAlgHom)
  let v : coordinate K := -MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1
  have ht : AlgHom.mapDomain q t = toConv (Coroot.simpleCorootMap G i).toAlgHom := by
    rfl
  have hu : AlgHom.mapDomain q (gaParameterPoint (simpleBorelRootMap G i) v) =
      gaParameterPoint (G.simpleRootMap i) v := by
    unfold gaParameterPoint
    rw [← MonoidHom.comp_apply, ← AlgHom.mapDomain_comp, simpleBorelRootMap_comp]
  change (AlgHom.mapDomain q (t * gaParameterPoint (simpleBorelRootMap G i) v)).ofConv = _
  rw [map_mul, ht, hu]

end SchubertGeometry.ProjectiveLine
