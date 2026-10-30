import OrbitComplexity.SchubertGeometry.ProjectiveLine.TorusParameters
import OrbitComplexity.SchubertGeometry.ProjectiveLine.PolynomialChart
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms

/-! # Torus translations of the simple Schubert projective line -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti Topology
universe u
variable {K : Type u} [Field K]

private def gaPolynomialMorphism :
    (additiveVariety K).toOver ⟶ (affineVariety K (Polynomial K)).toOver :=
  affineMorphism (Polynomial.aeval (SymmetricAlgebra.ι K K 1))

private theorem gaPolynomial_points (t : K) :
    Variety.mapPoints (gaPolynomialMorphism (K := K)) (additivePointsEquiv K t) =
      (affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval t) := by
  let p := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  change Variety.mapPoints (affineMorphism (Polynomial.aeval (SymmetricAlgebra.ι K K 1)))
      ((affineVarietyPointsEquiv K _).symm p) = _
  rw [affineMorphism_points]
  apply (affineVarietyPointsEquiv K (Polynomial K)).injective
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Polynomial.algHom_ext
  change p ((Polynomial.aeval (SymmetricAlgebra.ι K K 1)) Polynomial.X) =
    (Polynomial.aeval t) Polynomial.X
  rw [Polynomial.aeval_X, Polynomial.aeval_X]
  exact AdditiveGroup.gaPointsMulEquiv_symm_apply_ι (Multiplicative.ofAdd t)

private theorem polynomialScale_points (c : Kˣ) (t : K) :
    Variety.mapPoints (affineMorphism (Polynomial.algEquivCMulXAddC (c : K) 0).toAlgHom)
      ((affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval t)) =
    (affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval ((c : K) * t)) := by
  rw [affineMorphism_points]
  congr 1
  apply Polynomial.algHom_ext
  change (Polynomial.aeval t) (Polynomial.algEquivCMulXAddC (c : K) 0 Polynomial.X) =
    (Polynomial.aeval ((c : K) * t)) Polynomial.X
  simp

variable [IsAlgClosed K]

private theorem gaPolynomial_scaling (c : Kˣ) :
    (additiveScaleIso (c : K) c.ne_zero).hom ≫ gaPolynomialMorphism =
      gaPolynomialMorphism ≫ affineMorphism (Polynomial.algEquivCMulXAddC (c : K) 0).toAlgHom := by
  apply Variety.mapPoints_injective
  funext q
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective q
  simp only [Variety.mapPoints_comp, additiveScaleIso_points]
  rw [gaPolynomial_points, gaPolynomial_points, polynomialScale_points]

private def projectiveScalingOver (c : Kˣ) :
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver ≅
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  Over.isoMk (projectiveLineScalingIso c) (projectiveLineScaling_base c)

private theorem factor_scaling {A B C : Scheme.{u}}
    (j : A ⟶ C) (q : A ⟶ B) (c : B ⟶ C)
    (l : A ⟶ A) (s : B ⟶ B) (m : C ⟶ C)
    (hj : j = q ≫ c) (hq : l ≫ q = q ≫ s) (hc : s ≫ c = c ≫ m) :
    j ≫ m = l ≫ j := by
  rw [hj, Category.assoc, ← hc, ← Category.assoc, ← hq, Category.assoc]

private theorem projectiveGaChart_scale (c : Kˣ) :
    projectiveLineChart K ⟨0⟩ ≫ (projectiveScalingOver c).hom =
      (additiveScaleIso (c : K) c.ne_zero).hom ≫ projectiveLineChart K ⟨0⟩ := by
  have h := congrArg Over.Hom.left (gaPolynomial_scaling c)
  change (additiveScaleIso (c : K) c.ne_zero).hom.left ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) =
    Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.algEquivCMulXAddC (c : K) 0).toRingHom) at h
  apply Over.OverMorphism.ext
  exact factor_scaling _ _ _ _ _ _ (projectiveLineChart_polynomial K ⟨0⟩) h
    (projectiveLineScaling_chart c)

private theorem eq_of_open_chart {X Y : Variety K} [PreirreducibleSpace X.scheme]
    (c : (additiveVariety K).toOver ⟶ X.toOver) [IsOpenImmersion c.left]
    (f g : X.toOver ⟶ Y.toOver) (he : c ≫ f = c ≫ g) : f = g := by
  have hf : f.left ≫ Y.toSpec = X.toSpec := f.w
  have hg : g.left ≫ Y.toSpec = X.toSpec := g.w
  have : LocallyOfFiniteType (f.left ≫ Y.toSpec) := by rw [hf]; infer_instance
  have : IsReduced X.toOver.left := X.reduced
  have : PreirreducibleSpace X.toOver.left := inferInstanceAs (PreirreducibleSpace X.scheme)
  have hne : (Set.range c.left).Nonempty :=
    ⟨c.left ((additiveVariety K).pointMap (additivePointsEquiv K 0)), _, rfl⟩
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq Y.toSpec (Set.range c.left)
    c.left.isOpenEmbedding.2.isLocallyClosed (c.left.isOpenEmbedding.2.dense hne)
  · rintro x ⟨z, rfl⟩ _
    exact congrArg (fun k => k z) (congrArg Over.Hom.left he)
  · exact hf.trans hg.symm

private theorem chartScaleAction_transport {X P : Variety K} [PreirreducibleSpace X.scheme]
    (c : (additiveVariety K).toOver ⟶ X.toOver) [IsOpenImmersion c.left]
    (d : (additiveVariety K).toOver ⟶ P.toOver) (e : X.toOver ≅ P.toOver)
    (a : K) (ha : a ≠ 0) (f : X.toOver ⟶ X.toOver) (g : P.toOver ⟶ P.toOver)
    (hce : c ≫ e.hom = d)
    (hf : c ≫ f = (additiveScaleIso a ha).hom ≫ c)
    (hg : d ≫ g = (additiveScaleIso a ha).hom ≫ d) :
    f ≫ e.hom = e.hom ≫ g := by
  apply eq_of_open_chart c
  rw [← Category.assoc, hf, Category.assoc, hce, ← hg, ← hce, Category.assoc]

variable [CharZero K] (G : ReductiveGroupData K)

private def torusLeviPoint (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨AlgHom.mapDomain G.torusSplit z, G.torus_le_leviPoints {i}
      (mapDomain_mem_torusPoints G.torusIdeal G.torusSplit G.split_surjective G.split_eq_zero z)⟩

/-- The selected torus acts through the diagonal projective automorphism of its root character. -/
theorem simpleSchubertIso_torus (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    ∃ c : Kˣ, (c : K) = z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1) ∧
      Variety.translateMorphism (leviVariety G {i})
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
          ((leviPointsMulEquiv G {i}).symm
            ⟨AlgHom.mapDomain G.torusSplit z, G.torus_le_leviPoints {i}
              (mapDomain_mem_torusPoints G.torusIdeal G.torusSplit
                G.split_surjective G.split_eq_zero z)⟩) ≫ (simpleSchubertIso G i).hom =
        (simpleSchubertIso G i).hom ≫
          (Over.isoMk (projectiveLineScalingIso c) (projectiveLineScaling_base c)).hom := by
  have hn : z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1) ≠ 0 :=
    (simplePositiveChart_torus G i z).1
  let c : Kˣ := Units.mk0 _ hn
  refine ⟨c, rfl, ?_⟩
  change Variety.translateMorphism (leviVariety G {i})
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (torusLeviPoint G i z) ≫ (simpleSchubertIso G i).hom =
    (simpleSchubertIso G i).hom ≫ (projectiveScalingOver c).hom
  exact chartScaleAction_transport (simplePositiveChart G i) (projectiveLineChart K ⟨0⟩)
    (simpleSchubertIso G i) (c : K) c.ne_zero
    (Variety.translateMorphism (leviVariety G {i})
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) (torusLeviPoint G i z))
    (projectiveScalingOver c).hom (simpleSchubertIso_positive G i)
    ((simplePositiveChart_torus G i z).2 c.ne_zero) (projectiveGaChart_scale c)

end SchubertGeometry
