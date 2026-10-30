import OrbitComplexity.SchubertGeometry.Roots.ElementSystem
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootParameters
import OrbitComplexity.ReductiveGroups.Groups.Representatives.Inverse

/-! # Compatible root elements and inverse-simple representatives -/

noncomputable section
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem root_exists_simple (r : G.rootIndex) :
    ∃ w : G.weylGroup, ∃ i : G.rootBase.support,
      G.rootSystem.weylGroupToPerm w i.val = r := by
  apply G.rootBase.induction_reflect r
  · intro r hr
    obtain ⟨w, i, hi⟩ := hr
    refine ⟨RootPairing.weylGroup.ofIdx G.rootSystem r * w, i, ?_⟩
    change G.rootSystem.reflectionPerm r (G.rootSystem.weylGroupToPerm w i.val) = _
    rw [hi]
  · intro r hr
    exact ⟨1, ⟨r, hr⟩, rfl⟩
  · intro r j hr _
    obtain ⟨w, i, hi⟩ := hr
    refine ⟨RootPairing.weylGroup.ofIdx G.rootSystem j * w, i, ?_⟩
    change G.rootSystem.reflectionPerm j (G.rootSystem.weylGroupToPerm w i.val) = _
    rw [hi]

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

omit [IsAlgClosed K] [CharZero K] in
private theorem torus_split (t : (torusVariety G).points) :
    (torusPointsMulEquiv G t : G.points) =
      AlgHom.mapDomain G.torusSplit (WithConv.toConv
        ((affinePointsEquiv.symm t).comp (torusCoordinateEquiv G).symm.toAlgHom)) := by
  rw [torusPointsMulEquiv_coe]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  change affinePointsEquiv.symm t (Ideal.Quotient.mk G.torusIdeal.toIdeal a) =
    affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm (G.torusSplit a))
  rw [← torusCoordinateEquiv_mk]
  exact congrArg (affinePointsEquiv.symm t) ((torusCoordinateEquiv G).symm_apply_apply _).symm

private theorem parameter_torus_mul (r : G.rootIndex)
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hm : gaAffineGroupTangent φ ∈ G.rootWeightSpace r)
    (t : (torusVariety G).points) (a : K) :
    (torusPointsMulEquiv G t : G.points) * gaParameterPoint φ a =
      gaParameterPoint φ (torusWeightCharacter G (G.rootCharacter r).toAdd t * a) *
        (torusPointsMulEquiv G t : G.points) := by
  have h := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
    (G.rootCharacter r) (WithConv.toConv
      ((affinePointsEquiv.symm t).comp (torusCoordinateEquiv G).symm.toAlgHom)) φ hm a
  rw [← torus_split G t] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

private theorem parameter_properties (r : G.rootIndex)
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hm : gaAffineGroupTangent φ ∈ G.rootWeightSpace r)
    (hn : gaAffineGroupTangent φ ≠ 0) (hc : Function.Surjective φ) :
    gaAffineGroupTangent φ ∈ G.rootWeightSpace r ∧
      gaAffineGroupTangent φ ≠ 0 ∧ Function.Surjective φ ∧
      IsClosedImmersion (gaMorphism G φ).left ∧
      Set.range (fun a : K => gaParameterPoint φ a) =
        (rootSubgroupPoints G r : Set G.points) := by
  refine ⟨hm, hn, hc, ?_, rootSubgroupPoints_eq_range G r φ hm hn⟩
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom))
  exact IsClosedImmersion.spec_of_surjective _ hc

omit [IsAlgClosed K] [CharZero K] in
private theorem range_of_signed {A : Type*} (f g : K → A) (ε : K)
    (hε : ε = 1 ∨ ε = -1) (he : ∀ a, f a = g (ε * a)) :
    Set.range f = Set.range g := by
  have hs : ∀ a : K, ε * (ε * a) = a := by
    intro a
    rcases hε with rfl | rfl <;> simp
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨ε * a, (he a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨ε * a, (he (ε * a)).trans (congrArg g (hs a))⟩

private theorem family_spec
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hm : ∀ r, gaAffineGroupTangent (φ r) ∈ G.rootWeightSpace r)
    (hn : ∀ r, gaAffineGroupTangent (φ r) ≠ 0)
    (hc : ∀ r, Function.Surjective (φ r))
    (hi : ∀ i : G.rootBase.support,
      φ i.val = G.simpleRootMap i ∧ φ (-i.val) = G.negativeSimpleRootMap i)
    (hu : ∀ (r : G.rootIndex) (ψ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K),
      gaAffineGroupTangent ψ ∈ G.rootWeightSpace r → gaAffineGroupTangent ψ ≠ 0 →
      ∃ c : Kˣ, ∀ a : K, gaParameterPoint ψ a = gaParameterPoint (φ r) ((c : K) * a))
    (hs : ∀ (w : G.weylGroup) (i : G.rootBase.support),
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
        (weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase w *
            gaParameterPoint (φ i.val) a *
            (weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
              G.rootBase w)⁻¹ =
          gaParameterPoint (φ (G.rootSystem.weylGroupToPerm w i.val)) (ε * a)) ∧
        (weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase w *
            gaParameterPoint (φ (-i.val)) a *
            (weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
              G.rootBase w)⁻¹ =
          gaParameterPoint (φ (-G.rootSystem.weylGroupToPerm w i.val)) (ε * a))) :
    IsRootElementSystem G φ (fun r => φ (-r)) := by
  dsimp only [IsRootElementSystem]
  have hrep := G.inverseRepresentative_properties
  refine ⟨fun r => rfl, fun r => parameter_properties G r (φ r) (hm r) (hn r) (hc r),
    hi, (fun i => inferInstance), ?_, ?_, ?_, hrep.1, hrep.2.1,
    hrep.2.2.1, hrep.2.2.2, root_exists_simple G, ?_, ?_, hs, hu⟩
  · intro i a
    rw [simpleSl2Morphism_points, G.simpleSl2Points_upper i a, (hi i).1]
    rfl
  · intro i a
    rw [simpleSl2Morphism_points, G.simpleSl2Points_lower i a, (hi i).2]
    rfl
  · intro i
    rw [simpleSl2Morphism_points, G.simpleSl2Points_weyl i]
  · intro w i
    obtain ⟨ε, hε, he⟩ := hs w i
    exact (range_of_signed _ _ ε hε (fun a => (he a).1)).trans
      (rootSubgroupPoints_eq_range G _ _ (hm _) (hn _))
  · intro w i
    obtain ⟨ε, hε, he⟩ := hs w i
    exact (range_of_signed _ _ ε hε (fun a => (he a).2)).trans
      (rootSubgroupPoints_eq_range G _ _ (hm _) (hn _))

private theorem normalized_nonzero
    (x : LieModule.Weight K G.cartan G.centerQuotient → G.centerQuotient)
    (hx : IsSl2System x)
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hq : ∀ r, centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r)) = x r.val)
    (r : G.rootIndex) : gaAffineGroupTangent (φ r) ≠ 0 := by
  intro hz
  have h := hq r
  rw [hz, map_zero] at h
  exact hx.ne_zero r.val (LieSubalgebra.isNonZero_coe_root r) h.symm

/-- One family supplies root elements, inverse-simple representatives and torus scaling. -/
theorem root_elements_and_torus :
  ∃ X Y : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K,
    IsRootElementSystem G X Y ∧
    ∀ (r : G.rootIndex) (t : (torusVariety G).points) (a : K),
      (torusPointsMulEquiv G t : G.points) * gaParameterPoint (X r) a =
        gaParameterPoint (X r) (torusWeightCharacter G (G.rootCharacter r).toAdd t * a) *
          (torusPointsMulEquiv G t : G.points) :=
  Exists.elim G.exists_pairedRootParameters fun ω hω =>
    Exists.elim hω fun x hx' =>
      Exists.elim hx' fun φ hφ =>
        ⟨φ, (fun r => φ (-r)),
          family_spec G φ (fun r => (hφ.2.1 r).1)
            (normalized_nonzero G x hφ.1.toIsSl2System φ (fun r => (hφ.2.1 r).2.1))
            (fun r => (hφ.2.1 r).2.2) hφ.2.2.1 hφ.2.2.2.1
            (fun w i => by
              simpa only [weylElementPoint, simpleWeylWord_chosenReducedWord] using
                hφ.2.2.2.2.2 (chosenReducedWord G.rootBase w) i.val),
          fun r t a => parameter_torus_mul G r (φ r) (hφ.2.1 r).1 t a⟩

end SchubertGeometry
