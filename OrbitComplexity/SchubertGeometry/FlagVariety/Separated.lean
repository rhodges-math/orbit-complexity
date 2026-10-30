import OrbitComplexity.SchubertGeometry.FlagVariety.ClosedGraphs
import OrbitComplexity.SchubertGeometry.FlagVariety.Gluing
import OrbitComplexity.GroupActions.Varieties.AtlasSeparated

/-! # Separatedness of the flag scheme

Closed overlap graphs identify the diagonal locally on the translated affine atlas.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private def overlapProductIso (g h : G.points) :
    pullback (flagSchemeChart G g ≫ flagSchemeToSpec G)
      (flagSchemeChart G h ≫ flagSchemeToSpec G) ≅ (flagChartProduct G).scheme := by
  change _ ≅ pullback (GroupActions.oppositeUnipotentVariety G).toSpec
    (GroupActions.oppositeUnipotentVariety G).toSpec
  exact pullback.congrHom (flagSchemeChart_toSpec G g) (flagSchemeChart_toSpec G h)

private theorem overlapProductIso_fst (g h : G.points) :
    (overlapProductIso G g h).hom ≫ (flagChartFst G).left =
      pullback.fst (flagSchemeChart G g ≫ flagSchemeToSpec G)
        (flagSchemeChart G h ≫ flagSchemeToSpec G) := by
  change (pullback.congrHom (flagSchemeChart_toSpec G g)
      (flagSchemeChart_toSpec G h)).hom ≫ pullback.fst _ _ = _
  simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]

private theorem overlapProductIso_snd (g h : G.points) :
    (overlapProductIso G g h).hom ≫ (flagChartSnd G).left =
      pullback.snd (flagSchemeChart G g ≫ flagSchemeToSpec G)
        (flagSchemeChart G h ≫ flagSchemeToSpec G) := by
  change (pullback.congrHom (flagSchemeChart_toSpec G g)
      (flagSchemeChart_toSpec G h)).hom ≫ pullback.snd _ _ = _
  simp only [pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]

private theorem overlapGraph_eq (g h : G.points) :
    GroupActions.gluedOverlapGraph (flagGlueData G) (flagSchemeToSpec G) g h ≫
      (overlapProductIso G g h).hom = (flagOverlapGraph G g h).left := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => GroupActions.gluedOverlapGraph (flagGlueData G)
        (flagSchemeToSpec G) g h ≫ f) (overlapProductIso_fst G g h)).trans
        ((GroupActions.gluedOverlapGraph_fst (flagGlueData G)
          (flagSchemeToSpec G) g h).trans
          (congrArg Over.Hom.left (flagOverlapGraph_fst G g h)).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => GroupActions.gluedOverlapGraph (flagGlueData G)
        (flagSchemeToSpec G) g h ≫ f) (overlapProductIso_snd G g h)).trans
        ((GroupActions.gluedOverlapGraph_snd (flagGlueData G)
          (flagSchemeToSpec G) g h).trans
          (congrArg Over.Hom.left (flagOverlapGraph_snd G g h)).symm))

/-- The flag scheme is separated over the base field. -/
instance flagScheme_separated : IsSeparated (flagSchemeToSpec G) := by
  apply GroupActions.separated_of_glued_graphs (flagGlueData G) (flagSchemeToSpec G)
  intro g h
  change G.points at g h
  have hc : IsClosedImmersion
      (GroupActions.gluedOverlapGraph (flagGlueData G) (flagSchemeToSpec G) g h ≫
        (overlapProductIso G g h).hom) := by
    rw [overlapGraph_eq]
    exact flagOverlapGraph_isClosed G g h
  exact (@MorphismProperty.cancel_right_of_respectsIso Scheme _ @IsClosedImmersion _ _ _ _
    (GroupActions.gluedOverlapGraph (flagGlueData G) (flagSchemeToSpec G) g h)
      (overlapProductIso G g h).hom (overlapProductIso G g h).isIso_hom).mp hc

end
end SchubertGeometry