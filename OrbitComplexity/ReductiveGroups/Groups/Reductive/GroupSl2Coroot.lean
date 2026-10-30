import OrbitComplexity.ReductiveGroups.Groups.SL2.Diagonal
import OrbitComplexity.ReductiveGroups.Groups.Tangents.MultiplicativeMorphisms

/-! # Identification of the integrated SL2 diagonal with the simple coroot -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The diagonal restriction of the chosen SL2 morphism is the full-lattice simple coroot. -/
theorem simpleSl2Map_diagonal (i : G.rootBase.support) :
    (SimpleDiagonal.coordinateMap K).comp (G.simpleSl2Map i) =
      Coroot.simpleCorootMap G i := by
  apply gmMorphism_ext_of_tangent_eq
  rw [derivationComp_comp, LinearMap.comp_apply, SimpleDiagonal.coordinateMap_differential,
    G.simpleSl2Map_differential, Coroot.simpleCorootMap_differential]
  change G.simpleSl2LieHom i (TauCeti.slFinTwoBasis K (2 : Fin 3)) =
    ⁅gaAffineGroupTangent (G.simpleRootMap i),
      gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆
  simpa using G.simpleSl2LieHom_basis i (2 : Fin 3)


/-- The integrated diagonal at every unit equals the simple coroot in the full group. -/
theorem simpleSl2Points_diagonal (i : G.rootBase.support) (u : Kˣ) :
    G.simpleSl2Points i (Matrix.SpecialLinearGroup.diag2 (u : K) (Units.ne_zero u)) =
      Coroot.simpleCorootPoint G i u := by
  change AlgHom.mapDomain (G.simpleSl2Map i)
    ((SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm
      (Matrix.SpecialLinearGroup.diag2 (u : K) (Units.ne_zero u))) = _
  rw [← SimpleDiagonal.coordinateMap_point K u, Coroot.simpleCorootPoint_map]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  exact congrArg
    ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u)).ofConv
    (congrArg (fun phi : G.coordinateAlgebra →ₐc[K] MonoidAlgebra K (Multiplicative ℤ) =>
      phi a) (G.simpleSl2Map_diagonal i))

end ReductiveGroups.ReductiveGroupData
