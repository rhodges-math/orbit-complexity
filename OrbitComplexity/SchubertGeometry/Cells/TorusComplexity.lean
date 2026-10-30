import OrbitComplexity.SchubertGeometry.Levi.CellComplexity
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.GroupActions.Complexity.Toric
import OrbitComplexity.GroupActions.Actions.EquivariantPoints

/-! # Torus complexity on Schubert cells and closures

The cell inclusion is torus-equivariant and the top cell is a dense open subvariety
of its Schubert closure. Minimum torus orbit codimension is therefore preserved.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f = Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

/-- A lower Schubert cell includes torus-equivariantly into a containing Schubert variety. -/
instance schubertCellOfLE_torus (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) :
    IsModHom (torusVariety G).toOver (schubertCellOfLE G u w huw) := by
  let f := schubertCellOfLE G u w huw
  have hfp (p : (schubertCell G u).points) :
      Variety.mapPoints (schubertInclusion G w) (Variety.mapPoints f p) =
        Variety.mapPoints (schubertCellInclusion G u) p := by
    have hc := Variety.mapPoints_comp (X := schubertCell G u) (Y := schubertVariety G w)
      (Z := flagVariety G) f (schubertInclusion G w) p
    have hf := congrArg (fun g : (schubertCell G u).toOver ⟶ (flagVariety G).toOver =>
      Variety.mapPoints (X := schubertCell G u) (Y := flagVariety G) g p)
      (schubertCellOfLE_comp G u w huw)
    exact hc.symm.trans hf
  apply Variety.isModHom_of_points (torusVariety G) (schubertCell G u)
    (schubertVariety G w) f
  intro t q
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  exact (hfp (t • q)).trans
    ((equivariant_points (schubertCellInclusion G u) t q).trans
      ((congrArg (fun p : (flagVariety G).points => t • p) (hfp q).symm).trans
        (equivariant_points (schubertInclusion G w) t (Variety.mapPoints f q)).symm))

/-- The top cell and its Schubert closure have equal torus complexity. -/
theorem torus_cell_complexity (w : G.weylGroup) :
    torusComplexity G (schubertCell G w) = torusComplexity G (schubertVariety G w) :=
  Variety.minOrbitCodim_eq_of_openImmersion (torusVariety G) (schubertCell G w)
    (schubertVariety G w) (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w))

end SchubertGeometry
