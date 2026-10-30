import OrbitComplexity.GroupActions.Rosenlicht.AffineRelations
import OrbitComplexity.GroupActions.Rosenlicht.FractionKernels
import OrbitComplexity.GroupActions.Rosenlicht.RelationFields
import OrbitComplexity.GroupActions.Rosenlicht.RelationKernels
import OrbitComplexity.GroupActions.Rosenlicht.ChartGerms

/-!
# Function-field coordinates of affine relation charts
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]
variable (U V : X.scheme.Opens) [Nonempty U] [Nonempty V]

omit [IsAlgClosed K] in
private theorem varietyIntegralProof : IsIntegral X.scheme :=
  isIntegral_of_irreducibleSpace_of_isReduced X.scheme

private theorem chartIntegralProof : IsIntegral (relationChart H X U V) :=
  relationChart_isIntegral H X U V (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.val, x.property⟩) (by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact ⟨x.val, x.property⟩)

private theorem chartDominantProof : IsDominant (relationChartInclusion H X U V) :=
  relationChartInclusion_dominant H X U V (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.val, x.property⟩) (by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact ⟨x.val, x.property⟩)

private theorem firstDominantProof : IsDominant (relationChartFirst H X U V) :=
  relationChartFirst_dominant H X U V (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.val, x.property⟩) (by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact ⟨x.val, x.property⟩)

private theorem secondDominantProof : IsDominant (relationChartSecond H X U V) :=
  relationChartSecond_dominant H X U V (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.val, x.property⟩) (by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact ⟨x.val, x.property⟩)

private theorem openDominantProof {T : Scheme.{u}} [IrreducibleSpace T]
    (W : T.Opens) [Nonempty W] : IsDominant W.ι :=
  Opens.isDominant_ι (W.isOpen.dense (by
    obtain ⟨x⟩ := (inferInstance : Nonempty W)
    exact ⟨x.val, x.property⟩))

attribute [local instance] varietyIntegralProof chartIntegralProof chartDominantProof
  firstDominantProof
  secondDominantProof openDominantProof

/-- Sections of the first coordinate chart act on the coordinate algebra of
the relation chart through its first projection. -/
@[instance_reducible]
def relationChartAlgebra : Algebra Γ(X.scheme, U) Γ(relationChart H X U V, ⊤) :=
  (U.topIso.inv ≫ (relationChartFirst H X U V).appTop).hom.toAlgebra

/-- A regular coordinate tuple on the second chart pulls back to a polynomial
map into the coordinate algebra of the relation chart. -/
def relationChartCoordinates {ι : Type v} (c : ι → Γ(X.scheme, V)) :
    let : Algebra Γ(X.scheme, U) Γ(relationChart H X U V, ⊤) :=
      relationChartAlgebra H X U V
    MvPolynomial ι Γ(X.scheme, U) →ₐ[Γ(X.scheme, U)] Γ(relationChart H X U V, ⊤) :=
  let : Algebra Γ(X.scheme, U) Γ(relationChart H X U V, ⊤) :=
    relationChartAlgebra H X U V
  MvPolynomial.aeval (fun i ↦ (relationChartSecond H X U V).appTop (V.topIso.inv (c i)))

/-- The first relation-field pullback of a regular function is the germ of
its first-coordinate pullback on the relation chart. -/
theorem relationChartFirst_germ (s : Γ(X.scheme, U)) :
    functionFieldMap (relationChartInclusion H X U V)
      (relationFirstFieldMap H X (X.scheme.germToFunctionField U s)) =
      (relationChart H X U V).germToFunctionField ⊤
        ((relationChartFirst H X U V).appTop (U.topIso.inv s)) := by
  change functionFieldMap (relationChartInclusion H X U V)
    (functionFieldMap ((orbitRelationProjection H X).left :
      (orbitRelationVariety H X).scheme ⟶ X.scheme)
      (X.scheme.germToFunctionField U s)) = _
  rw [← RingHom.comp_apply, ← functionFieldMap_comp]
  rw [functionFieldMap_congr _ _ (relationChartFirst_fac H X U V).symm]
  rw [functionFieldMap_comp, RingHom.comp_apply]
  have hu := openFunctionFieldMap_germ (X := X.scheme) U s
  exact (congrArg (functionFieldMap (relationChartFirst H X U V)) hu).trans
    (functionFieldMap_appTop (relationChartFirst H X U V) (U.topIso.inv s))

/-- The second relation-field pullback of a regular function is the germ of
its second-coordinate pullback on the relation chart. -/
theorem relationChartSecond_germ (s : Γ(X.scheme, V)) :
    functionFieldMap (relationChartInclusion H X U V)
      (relationSecondFieldMap H X (X.scheme.germToFunctionField V s)) =
      (relationChart H X U V).germToFunctionField ⊤
        ((relationChartSecond H X U V).appTop (V.topIso.inv s)) := by
  change functionFieldMap (relationChartInclusion H X U V)
    (functionFieldMap ((orbitRelationSecond H X).left :
      (orbitRelationVariety H X).scheme ⟶ X.scheme)
      (X.scheme.germToFunctionField V s)) = _
  rw [← RingHom.comp_apply, ← functionFieldMap_comp]
  rw [functionFieldMap_congr _ _ (relationChartSecond_fac H X U V).symm]
  rw [functionFieldMap_comp, RingHom.comp_apply]
  have hu := openFunctionFieldMap_germ (X := X.scheme) V s
  exact (congrArg (functionFieldMap (relationChartSecond H X U V)) hu).trans
    (functionFieldMap_appTop (relationChartSecond H X U V) (V.topIso.inv s))

/-- The regular relation ideal on two affine coordinate charts becomes the
polynomial relation ideal of the generic orbit after passing to the first
chart's fraction field. -/
theorem relationChart_kernel (hU : IsAffineOpen U) {ι : Type v}
    (c : ι → Γ(X.scheme, V)) :
    let := relationChartAlgebra H X U V
    (RingHom.ker (relationChartCoordinates H X U V c)).map
      (MvPolynomial.map (X.scheme.germToFunctionField U).hom) =
      genericOrbitIdeal H X (fun i ↦ X.scheme.germToFunctionField V (c i)) := by
  let R := Γ(X.scheme, U)
  let A := Γ(relationChart H X U V, ⊤)
  let F := X.scheme.functionField
  let L := (relationChart H X U V).functionField
  let := relationChartAlgebra H X U V
  let : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let : IsFractionRing R F :=
    functionField_isFractionRing_of_isAffineOpen X.scheme U hU
  let : Algebra R L :=
    (((relationChart H X U V).germToFunctionField ⊤).hom.comp (algebraMap R A)).toAlgebra
  let i : F →ₐ[R] L :=
    { __ := (functionFieldMap (relationChartInclusion H X U V)).comp
        (relationFirstFieldMap H X)
      commutes' := fun s ↦ by
        change functionFieldMap (relationChartInclusion H X U V)
          (relationFirstFieldMap H X (X.scheme.germToFunctionField U s)) = _
        exact relationChartFirst_germ H X U V s }
  let j : A →ₐ[R] L :=
    { __ := ((relationChart H X U V).germToFunctionField ⊤).hom
      commutes' := fun _ ↦ rfl }
  let f := relationChartCoordinates H X U V c
  have hfrac := ker_fraction_polynomial R F A L i j
    ((relationChart H X U V).germToFunctionField_injective ⊤) f
  change RingHom.ker (MvPolynomial.eval₂Hom i.toRingHom
      (fun s ↦ j (f (MvPolynomial.X s)))) =
    (RingHom.ker (relationChartCoordinates H X U V c)).map
      (MvPolynomial.map (X.scheme.germToFunctionField U).hom) at hfrac
  rw [← hfrac]
  let : Algebra F (orbitRelationVariety H X).scheme.functionField :=
    (relationFirstFieldMap H X).toAlgebra
  let ev : MvPolynomial ι F →ₐ[F] (orbitRelationVariety H X).scheme.functionField :=
    MvPolynomial.aeval (fun k ↦ relationSecondFieldMap H X
      (X.scheme.germToFunctionField V (c k)))
  have he : (functionFieldMap (relationChartInclusion H X U V)).comp ev.toRingHom =
      MvPolynomial.eval₂Hom i.toRingHom (fun k ↦ j (f (MvPolynomial.X k))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change functionFieldMap (relationChartInclusion H X U V) (ev (MvPolynomial.C a)) = i a
      rw [show ev (MvPolynomial.C a) = relationFirstFieldMap H X a from ev.commutes a]
      rfl
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change functionFieldMap (relationChartInclusion H X U V)
        (ev (MvPolynomial.X k)) = j (f (MvPolynomial.X k))
      simp only [ev, f, relationChartCoordinates, MvPolynomial.aeval_X]
      change functionFieldMap (relationChartInclusion H X U V)
        (relationSecondFieldMap H X (X.scheme.germToFunctionField V (c k))) =
        (relationChart H X U V).germToFunctionField ⊤
          ((relationChartSecond H X U V).appTop (V.topIso.inv (c k)))
      exact relationChartSecond_germ H X U V (c k)
  rw [← he, RingHom.ker_comp_of_injective ev.toRingHom
    (functionFieldMap (relationChartInclusion H X U V)).injective]
  exact relationField_ker_eq H X (fun k ↦ X.scheme.germToFunctionField V (c k))

end

end GroupActions.Variety
