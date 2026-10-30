import OrbitComplexity.SchubertGeometry.Levi.BorelOrbits
import OrbitComplexity.SchubertGeometry.Levi.Reductive
import OrbitComplexity.GroupActions.Complexity.Basic
import OrbitComplexity.GroupActions.Actions.RestrictionOrbits

/-! # The chosen Borel of a standard Levi

The quotient coordinate isomorphism identifies the chosen Borel of the reductive
Levi data with the Levi--Borel intersection. Its inclusion square identifies the
restricted actions and their minimum orbit codimensions on Schubert varieties.
-/

open CategoryTheory GroupActions MonoidalCategory AlgebraicGeometry
open scoped MonoidalLeftAction

noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K]

private theorem scalarRestriction_comp {H B L X : Variety K}
    [GrpObj H.toOver] [GrpObj B.toOver] [GrpObj L.toOver]
    [ModObj L.toOver X.toOver] (f : H.toOver ⟶ B.toOver) (g : B.toOver ⟶ L.toOver)
    [IsMonHom f] [IsMonHom g] :
    (letI := Mod.scalarRestriction g X.toOver
     Mod.scalarRestriction f X.toOver) = Mod.scalarRestriction (f ≫ g) X.toOver := by
  dsimp only [Mod.scalarRestriction]
  congr 1
  change f ⊵ₗ X.toOver ≫ (g ⊵ₗ X.toOver ≫ ModObj.smul) =
    (f ≫ g) ⊵ₗ X.toOver ≫ ModObj.smul
  rw [MonoidalLeftAction.comp_actionHomLeft, Category.assoc]

open ReductiveGroups TauCeti
variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem borelQuotientIso_comp (I : Set G.rootBase.support) :
    CommHopfAlgCat.mkQuotient (G.leviAlgebra I).obj (leviBorelIdealInLevi G I) ≫
        (leviBorelQuotientIso G I).hom =
      CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra)
        (G.leviIdeal_le_leviBorel I) :=
  CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- The Levi--Borel variety is the chosen Borel variety of the reductive Levi data. -/
def leviBorelIso (I : Set G.rootBase.support) :
    (leviBorelVariety G I).toOver ≅ (borelVariety (leviGroupData G I)).toOver :=
  (Grp.forget _).mapIso
    ((hopfSpec (CommRingCat.of K)).mapIso (leviBorelQuotientIso G I).op)

/-- The isomorphism to the chosen Levi Borel preserves multiplication. -/
instance leviBorelIso_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (leviBorelIso G I).hom := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (leviBorelQuotientIso G I).hom.op).hom.hom)
  infer_instance

/-- The Borel identification commutes with the inclusions into the Levi variety. -/
theorem leviBorelIso_comp (I : Set G.rootBase.support) :
    (leviBorelIso G I).hom ≫ borelInclusion (leviGroupData G I) =
      leviBorelLeviInclusion G I := by
  change (((hopfSpec (CommRingCat.of K)).map
      (leviBorelQuotientIso G I).hom.op) ≫
    ((hopfSpec (CommRingCat.of K)).map
      (CommHopfAlgCat.mkQuotient (G.leviAlgebra I).obj
        (leviBorelIdealInLevi G I)).op)).hom.hom = _
  rw [← Functor.map_comp, ← CategoryTheory.op_comp, borelQuotientIso_comp]
  rfl

/-- Levi complexity is the minimum codimension for the Levi--Borel action on a Schubert variety. -/
theorem levi_schubert_complexity (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      minOrbitCodim (leviBorelVariety G I) (schubertVariety G w) := by
  let : ModObj (reductiveVariety (leviGroupData G I)).toOver
      (schubertVariety G w).toOver :=
    inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
  have hmin :
      letI := Mod.scalarRestriction (borelInclusion (leviGroupData G I))
        (schubertVariety G w).toOver
      letI := Mod.scalarRestriction (leviBorelIso G I).hom (schubertVariety G w).toOver
      minOrbitCodim (leviBorelVariety G I) (schubertVariety G w) =
        complexity (leviGroupData G I) (schubertVariety G w) := by
    let := Mod.scalarRestriction (borelInclusion (leviGroupData G I))
      (schubertVariety G w).toOver
    exact Variety.restricted_minOrbitCodim (leviBorelIso G I).hom
      (Variety.pointsHomeomorph (leviBorelIso G I)).surjective (schubertVariety G w)
  have haction := scalarRestriction_comp (X := schubertVariety G w)
    (leviBorelIso G I).hom (borelInclusion (leviGroupData G I))
  simp only [leviBorelIso_comp] at haction
  rw [haction] at hmin
  exact hmin.symm.trans (leviBorel_restricted_minOrbitCodim G I w)

end SchubertGeometry
