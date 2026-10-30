import OrbitComplexity.SchubertGeometry.ProjectiveLine.RootParameters

/-! # Torus weights on the selected simple-root chart -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def characterValue (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) : K :=
  z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1)

private theorem characterValue_ne (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    characterValue G i z ≠ 0 := by
  apply left_ne_zero_of_mul_eq_one
    (b := z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val)⁻¹ 1))
  unfold characterValue
  rw [← map_mul, MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
    ← MonoidAlgebra.one_def, map_one]

private def torusLeviPoint (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨AlgHom.mapDomain G.torusSplit z, G.torus_le_leviPoints {i}
      (mapDomain_mem_torusPoints G.torusIdeal G.torusSplit G.split_surjective G.split_eq_zero z)⟩

private theorem torusLeviPoint_coe (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    (leviPointsMulEquiv G {i} (torusLeviPoint G i z) : G.points) =
      AlgHom.mapDomain G.torusSplit z := by
  simp only [torusLeviPoint, MulEquiv.apply_symm_apply]

private theorem torus_flag_parameter (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) (t : K) :
    flagProjection G (AlgHom.mapDomain G.torusSplit z *
      (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) =
    flagProjection G (gaParameterPoint (G.simpleRootMap i) (characterValue G i z * t) *
      (G.reflectionPoint i.val)⁻¹) := by
  let d := AlgHom.mapDomain G.torusSplit z
  let n := G.reflectionPoint i.val
  have hd : d ∈ G.torusPoints := mapDomain_mem_torusPoints G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero z
  have hn : n ∈ Subgroup.normalizer (G.torusPoints : Set G.points) :=
    G.isBruhatSystem.weyl.mem_normalizer i.val
  have ht := (Subgroup.mem_normalizer_iff.mp hn d⁻¹).mp (G.torusPoints.inv_mem hd)
  have he := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
    (G.rootCharacter i.val) z (G.simpleRootMap i) (G.simpleRootMap_tangent_mem i) t
  have hc : d * gaParameterPoint (G.simpleRootMap i) t * d⁻¹ =
      gaParameterPoint (G.simpleRootMap i) (characterValue G i z * t) := by
    simpa only [d, gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, characterValue] using he
  apply (flagProjection_eq_iff G _ _).mpr
  convert G.torus_le_borel ht using 1
  rw [← hc]
  dsimp only [d, n]
  group

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_smul {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (t : H.points) (q : X.points) :
    Variety.mapPoints f (t • q) = t • Variety.mapPoints f q := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (t • q) ≫ f = Y.pointsEquivOverHom (t • Variety.mapPoints f q)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom t) (X.pointsEquivOverHom q)

private theorem positiveChart_torus_points (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) (t : K) :
    torusLeviPoint G i z •
      Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K t) =
    Variety.mapPoints (simplePositiveChart G i)
      (additivePointsEquiv K (characterValue G i z * t)) := by
  apply Variety.mapPoints_injective_of_mono
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
  rw [equivariant_smul, leviFlag_smul, torusLeviPoint_coe,
    ← Variety.mapPoints_comp, ← Variety.mapPoints_comp,
    simplePositiveChart_points, simplePositiveChart_points, flagVarietyAction_points]
  exact congrArg (flagVarietyPointsEquiv G) (torus_flag_parameter G i z t)

omit [CharZero K] in
private theorem chart_scale {H X : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (f : (additiveVariety K).toOver ⟶ X.toOver)
    (g : H.points) (c : K) (hc : c ≠ 0)
    (h : ∀ t, g • Variety.mapPoints f (additivePointsEquiv K t) =
      Variety.mapPoints f (additivePointsEquiv K (c * t))) :
    f ≫ Variety.translateMorphism H X g = (additiveScaleIso c hc).hom ≫ f := by
  apply Variety.mapPoints_injective
  funext q
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective q
  simp only [Variety.mapPoints_comp, Variety.mapPoints_translateMorphism,
    additiveScaleIso_points]
  exact h t

omit [CharZero K] in
private theorem chart_scale_pair {H X : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (f : (additiveVariety K).toOver ⟶ X.toOver)
    (g : H.points) (c : K) (hc : c ≠ 0)
    (h : ∀ t, g • Variety.mapPoints f (additivePointsEquiv K t) =
      Variety.mapPoints f (additivePointsEquiv K (c * t))) :
    c ≠ 0 ∧ ∀ hc' : c ≠ 0,
      f ≫ Variety.translateMorphism H X g = (additiveScaleIso c hc').hom ≫ f :=
  ⟨hc, fun hc' => chart_scale f g c hc' h⟩

/-- A torus point scales the selected positive root parameter by its nonzero root character. -/
theorem simplePositiveChart_torus (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    type_of% (chart_scale_pair (H := leviVariety G {i})
      (X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (simplePositiveChart G i) (torusLeviPoint G i z) (characterValue G i z)
      (characterValue_ne G i z) (positiveChart_torus_points G i z)) :=
  chart_scale_pair (H := leviVariety G {i})
    (X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (simplePositiveChart G i) (torusLeviPoint G i z) (characterValue G i z)
    (characterValue_ne G i z) (positiveChart_torus_points G i z)

end SchubertGeometry
