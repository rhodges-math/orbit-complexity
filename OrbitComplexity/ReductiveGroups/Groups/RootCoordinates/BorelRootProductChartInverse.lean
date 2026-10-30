import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductChart
import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedPointClosure
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Borel Root Product Chart Inverse

The ordered Ga product quotient coordinate is an algebra
isomorphism from the original Ga-only closed subgroup coordinate quotient
onto a polynomial algebra, whenever its logarithm pullback is realized by
a polynomial automorphism. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u v
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
  {κ : Type v}

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

private theorem borelRootUnipotentQuotient_isReduced
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :
    IsReduced (B ⧸ (borelRootUnipotentHopfIdeal J π hπ).toIdeal) := by
  change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ))
  unfold borelRootUnipotentHopfIdeal
  infer_instance

/-- Every K-point of the original Ga-only closed subgroup coordinate
quotient is the ordered Ga product quotient coordinate followed by
evaluation at some parameter, provided a polynomial automorphism realizes
the logarithm coordinates of the ordered product. -/
theorem BorelRootProductQuotientCoordinate.exists_eval
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i))
    (φ : (B ⧸ (borelRootUnipotentHopfIdeal J π hπ).toIdeal) →ₐ[K] K) :
    ∃ a : κ → K, (MvPolynomial.aeval a).comp
      (borelRootProductQuotientCoordinate J π hπ x hx l) = φ := by
  let H := CommHopfAlgCat.of K B
  let U := borelRootUnipotentHopfIdeal J π hπ
  let q := (CommHopfAlgCat.mkQuotient H U).hom.toAlgHom
  let E := borelRootUnipotentExponentialEquiv J hJ π hπ
  have hgmem : WithConv.toConv (φ.comp q) ∈
      CommHopfAlgCat.quotientPointsSubgroup H U (CommAlgCat.of K K) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro b hb
    change φ (q b) = 0
    rw [show q b = 0 from (CommHopfAlgCat.mkQuotient_eq_zero_iff H U b).mpr hb,
      map_zero]
  let g : CommHopfAlgCat.quotientPointsSubgroup H U (CommAlgCat.of K K) :=
    ⟨WithConv.toConv (φ.comp q), hgmem⟩
  let c : κ → K := fun i => e.coord i (E.symm g)
  let a : κ → K := fun j => MvPolynomial.aeval c (F.symm (MvPolynomial.X j))
  have hac : ∀ i, MvPolynomial.aeval a (F (MvPolynomial.X i)) = c i := by
    have h1 : (MvPolynomial.aeval c).comp F.symm.toAlgHom = MvPolynomial.aeval a := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [MvPolynomial.aeval_X]
      rfl
    intro i
    rw [← h1, AlgHom.comp_apply]
    change MvPolynomial.aeval c (F.symm (F (MvPolynomial.X i))) = c i
    rw [AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]
  have hprod : (⟨(l.map (fun i => gaParameterPoint (x i) (a i))).prod,
      GaParameterPoint.prod_mem_of_tangent_mem_quotient x U hx l a⟩ :
        CommHopfAlgCat.quotientPointsSubgroup H U (CommAlgCat.of K K)) = g := by
    apply E.symm.injective
    apply e.ext_elem
    intro i
    rw [← e.coord_apply, ← e.coord_apply]
    rw [← borelRootProductLogarithm_eval J hJ π hπ x hx l (e.coord i) a, ← hF i, hac i]
  refine ⟨a, ?_⟩
  apply (AlgHom.cancel_right (CommHopfAlgCat.mkQuotient_surjective H U)).mp
  change (MvPolynomial.aeval a).comp
    ((borelRootProductQuotientCoordinate J π hπ x hx l).comp q) = φ.comp q
  rw [BorelRootProductQuotientCoordinate.comp_quotient, gaProductCoordinate_eval]
  exact congrArg (fun p : CommHopfAlgCat.quotientPointsSubgroup H U
    (CommAlgCat.of K K) => WithConv.ofConv p.val) hprod

/-- The logarithm coordinate map composed with the inverse polynomial
automorphism is a left inverse of the ordered Ga product quotient
coordinate on the original Ga-only closed subgroup coordinate quotient. -/
theorem BorelRootProductQuotientCoordinate.logarithm_comp
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i)) :
    (((CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom.toAlgHom.comp
        (borelRootLogarithmCoordinateMap J hJ π hπ e.coord)).comp
          F.symm.toAlgHom).comp
      (borelRootProductQuotientCoordinate J π hπ x hx l) = AlgHom.id K _ := by
  let _ := borelRootUnipotentQuotient_isReduced J π hπ
  have hQL := BorelRootProductQuotientCoordinate.comp_logarithm
    J hJ π hπ x hx l e F hF
  apply AlgHom.ext
  intro y
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro φ
  obtain ⟨a, ha⟩ := BorelRootProductQuotientCoordinate.exists_eval
    J hJ π hπ x hx l e F hF φ
  have h := DFunLike.congr_fun hQL
    (F.symm (borelRootProductQuotientCoordinate J π hπ x hx l y))
  rw [← ha, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply]
  exact congrArg (MvPolynomial.aeval a) (h.trans (F.apply_symm_apply _))

/-- The ordered Ga product quotient coordinate, packaged as an algebra
isomorphism from the original Ga-only closed subgroup coordinate quotient
onto the polynomial algebra. Its inverse is the logarithm coordinate map
followed by the inverse of the given polynomial automorphism. -/
def borelRootProductQuotientChart
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i)) :
    (B ⧸ (borelRootUnipotentHopfIdeal J π hπ).toIdeal) ≃ₐ[K]
      MvPolynomial κ K :=
  AlgEquiv.ofAlgHom (borelRootProductQuotientCoordinate J π hπ x hx l)
    (((CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom.toAlgHom.comp
        (borelRootLogarithmCoordinateMap J hJ π hπ e.coord)).comp
          F.symm.toAlgHom)
    (by
      have hQL := BorelRootProductQuotientCoordinate.comp_logarithm
        J hJ π hπ x hx l e F hF
      rw [← AlgHom.comp_assoc, hQL]
      apply AlgHom.ext
      intro z
      exact F.apply_symm_apply z)
    (BorelRootProductQuotientCoordinate.logarithm_comp J hJ π hπ x hx l e F hF)

/-- The forward map of the chart is the ordered Ga product
quotient coordinate. -/
@[simp] theorem borelRootProductQuotientChart_apply
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i))
    (y : B ⧸ (borelRootUnipotentHopfIdeal J π hπ).toIdeal) :
    borelRootProductQuotientChart J hJ π hπ x hx l e F hF y =
      borelRootProductQuotientCoordinate J π hπ x hx l y :=
  rfl

/-- The underlying algebra map of the chart is the ordered Ga product
quotient coordinate. -/
theorem borelRootProductQuotientChart_toAlgHom
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i)) :
    (borelRootProductQuotientChart J hJ π hπ x hx l e F hF).toAlgHom =
      borelRootProductQuotientCoordinate J π hπ x hx l :=
  AlgHom.ext fun _ => rfl

/-- The inverse of the chart is the logarithm coordinate map, pushed to
the original quotient, after the inverse polynomial automorphism. -/
theorem borelRootProductQuotientChart_symm_apply
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i))
    (z : MvPolynomial κ K) :
    (borelRootProductQuotientChart J hJ π hπ x hx l e F hF).symm z =
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom
        (borelRootLogarithmCoordinateMap J hJ π hπ e.coord (F.symm z)) :=
  rfl

end ReductiveGroups
