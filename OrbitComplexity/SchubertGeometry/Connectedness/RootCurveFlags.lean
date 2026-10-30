import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveGroup
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveParameters
import OrbitComplexity.SchubertGeometry.Cells.Schubert
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Coroot
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaSubgroupParameters
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-! # Stabilizers and reflected endpoints of root curves

The upper root parameter fixes a Weyl flag when its inverse Weyl transform is positive.
The diagonal fixes every Weyl flag. The Weyl element in the conjugated rank-one group
carries the initial flag to the flag indexed by the reflection in the transported root.
-/

noncomputable section

namespace SchubertGeometry

open ReductiveGroups GroupActions TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem representative_mul_action {Γ X : Type*} [Group Γ] [MulAction Γ X]
    (π : Γ → X) (hπ : ∀ g h, π (g * h) = g • π h)
    {g h t k : Γ} (he : g * h = t * k) (ht : t • π k = π k) :
    g • π h = π k :=
  (hπ g h).symm.trans ((congrArg π he).trans ((hπ t k).trans ht))

private theorem representative_inv_action {Γ W X : Type*}
    [Group Γ] [Group W] [MulAction Γ X] (p : W → Γ) (f : W → X)
    (hm : ∀ a x, p a • f x = f (a * x)) (a x : W) :
    (p a)⁻¹ • f x = f (a⁻¹ * x) := by
  have he : p a • f (a⁻¹ * x) = f x :=
    (hm a (a⁻¹ * x)).trans (congrArg f (mul_inv_cancel_left a x))
  exact (congrArg (fun z => (p a)⁻¹ • z) he.symm).trans (inv_smul_smul _ _)

private theorem factor_action {Γ X : Type*} [Group Γ] [MulAction Γ X]
    {g t h : Γ} {z y : X} (he : g = t * h)
    (hh : h • z = y) (ht : t • y = y) : g • z = y := by
  rw [he, mul_smul, hh, ht]

private theorem involution_inv_action {Γ W X : Type*}
    [Group Γ] [Group W] [MulAction Γ X] (f : W → X) (n : Γ) (s : W)
    (hs : s * s = 1) (hn : ∀ x, n • f x = f (s * x)) (x : W) :
    n⁻¹ • f x = f (s * x) := by
  have he : n • f (s * x) = f x :=
    (hn (s * x)).trans (congrArg f (by rw [← mul_assoc, hs, one_mul]))
  exact (congrArg (fun z => n⁻¹ • z) he.symm).trans (inv_smul_smul _ _)

private theorem conjugate_action {Γ W X : Type*}
    [Group Γ] [Group W] [MulAction Γ X] (p : W → Γ) (f : W → X)
    (hm : ∀ a x, p a • f x = f (a * x))
    (w s : W) (n : Γ) (hn : ∀ x, n • f x = f (s * x))
    {c : Γ} (hc : c = p w * n * (p w)⁻¹)
    {r : W} (hr : r = w * s * w⁻¹) (x : W) : c • f x = f (r * x) := by
  rw [hc, mul_smul, mul_smul, representative_inv_action p f hm, hn, hm, hr]
  exact congrArg f (by simp only [mul_assoc])

private theorem conjugate_mem {Γ : Type*} [Group Γ] (H : Subgroup Γ)
    (n g : Γ) {H' : Subgroup Γ} {a : Γ} (ha : a ∈ H')
    (he : a = n⁻¹ * g * (n⁻¹)⁻¹) (hH : H = H') : n⁻¹ * g * n ∈ H := by
  rw [hH]
  simpa only [he, inv_inv] using ha

/-- Every torus point fixes every rational Weyl flag. -/
theorem rootCurve_torus_fixes (t : G.points) (ht : t ∈ G.torusPoints)
    (x : G.weylGroup) :
    t • flagProjection G (G.weylPoint x) = flagProjection G (G.weylPoint x) := by
  apply rootCurve_coset_fixed G.borelPoints (G.weylPoint x) t
  exact G.torus_le_borel
    ((Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer x) t).mp ht)

/-- Multiplication of chosen Weyl representatives has its expected action on Weyl flags. -/
theorem rootCurve_weyl_mul (a x : G.weylGroup) :
    G.weylPoint a • flagProjection G (G.weylPoint x) =
      flagProjection G (G.weylPoint (a * x)) := by
  obtain ⟨t, ht, he⟩ :=
    G.isBruhatSystem.weyl.weylElementPoint_mul G.rootBase a x
  have he' : G.weylPoint a * G.weylPoint x = t * G.weylPoint (a * x) := by
    simpa only [G.weylPoint_eq] using he
  exact representative_mul_action (flagProjection G) (flagProjection_smul G)
    he' (rootCurve_torus_fixes G t ht (a * x))

/-- The inverse of a chosen Weyl representative acts by the inverse Weyl element. -/
theorem rootCurve_weyl_inv (a x : G.weylGroup) :
    (G.weylPoint a)⁻¹ • flagProjection G (G.weylPoint x) =
      flagProjection G (G.weylPoint (a⁻¹ * x)) := by
  exact representative_inv_action G.weylPoint
    (fun z => flagProjection G (G.weylPoint z)) (rootCurve_weyl_mul G) a x

private theorem simpleReflection_flag (i : G.rootBase.support) (x : G.weylGroup) :
    G.reflectionPoint i.val • flagProjection G (G.weylPoint x) =
      flagProjection G
        (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val * x)) := by
  obtain ⟨t, ht, he⟩ :=
    G.isBruhatSystem.weyl.simple_eq_mul_weylElementPoint G.rootBase i
  have he' : G.reflectionPoint i.val =
      t * G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
    simpa only [G.weylPoint_eq] using he
  exact factor_action he' (rootCurve_weyl_mul G _ x)
    (rootCurve_torus_fixes G t ht _)

private theorem inverseReflection_flag (i : G.rootBase.support) (x : G.weylGroup) :
    (G.reflectionPoint i.val)⁻¹ • flagProjection G (G.weylPoint x) =
      flagProjection G
        (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val * x)) := by
  exact involution_inv_action (fun z => flagProjection G (G.weylPoint z))
    (G.reflectionPoint i.val) (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    (RootPairing.weylGroup.ofIdx_mul_self G.rootSystem i.val)
    (simpleReflection_flag G i) x

/-- The point homomorphism of the simple rank-one group conjugated by a Weyl representative. -/
def rootSl2Points (w : G.weylGroup) (i : G.rootBase.support) :
    Matrix.SpecialLinearGroup (Fin 2) K →* G.points :=
  (MulAut.conj (G.weylPoint w)).toMonoidHom.comp (G.simpleSl2Points i)

/-- The conjugated rank-one homomorphism retains the specified upper parameter. -/
theorem rootSl2Points_upper (w : G.weylGroup) (i : G.rootBase.support) (t : K) :
    rootSl2Points G w i
      (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) =
      gaParameterPoint (rootUpperMap G w i) t := by
  change G.weylPoint w * G.simpleSl2Points i
      (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) *
        (G.weylPoint w)⁻¹ = gaParameterPoint (rootUpperMap G w i) t
  rw [G.simpleSl2Points_upper]
  exact (rootUpperMap_point G w i t).symm

/-- The conjugated rank-one homomorphism retains the specified lower parameter. -/
theorem rootSl2Points_lower (w : G.weylGroup) (i : G.rootBase.support) (t : K) :
    rootSl2Points G w i
      (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) =
      gaParameterPoint (rootLowerMap G w i) t := by
  change G.weylPoint w * G.simpleSl2Points i
      (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) *
        (G.weylPoint w)⁻¹ = gaParameterPoint (rootLowerMap G w i) t
  rw [G.simpleSl2Points_lower]
  exact (rootLowerMap_point G w i t).symm

/-- The conjugated Weyl matrix is the conjugate inverse simple reflection point. -/
theorem rootSl2Points_weyl (w : G.weylGroup) (i : G.rootBase.support) :
    rootSl2Points G w i (sl2Weyl K) =
      G.weylPoint w * (G.reflectionPoint i.val)⁻¹ * (G.weylPoint w)⁻¹ := by
  change G.weylPoint w * G.simpleSl2Points i (sl2Weyl K) *
    (G.weylPoint w)⁻¹ = _
  rw [G.simpleSl2Points_weyl]

/-- The conjugated Weyl matrix takes a Weyl flag to the flag of the transported reflection. -/
theorem rootSl2Points_weyl_flag (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) :
    rootSl2Points G w i (sl2Weyl K) • flagProjection G (G.weylPoint x) =
      flagProjection G (G.weylPoint
        (RootPairing.weylGroup.ofIdx G.rootSystem
          (G.rootSystem.weylGroupToPerm w i.val) * x)) := by
  exact conjugate_action G.weylPoint (fun z => flagProjection G (G.weylPoint z))
    (rootCurve_weyl_mul G) w (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    (G.reflectionPoint i.val)⁻¹ (inverseReflection_flag G i)
    (rootSl2Points_weyl G w i)
    (RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj G.rootSystem w i.val) x

/-- The simple coroot, evaluated at a unit, lies in the chosen maximal torus. -/
theorem rootCurve_coroot_mem (i : G.rootBase.support) (t : Kˣ) :
    Coroot.simpleCorootPoint G i t ∈ G.torusPoints := by
  exact mapDomain_mem_torusPoints G.torusIdeal G.torusSplit G.split_surjective
    G.split_eq_zero (Coroot.simpleCorootTorusPoint G i t)

/-- The conjugated rank-one diagonal is a point of the chosen maximal torus. -/
theorem rootSl2Points_diagonal_mem (w : G.weylGroup) (i : G.rootBase.support)
    (t : Kˣ) :
    rootSl2Points G w i (Matrix.SpecialLinearGroup.diag2 (t : K) t.ne_zero) ∈
      G.torusPoints := by
  change G.weylPoint w * G.simpleSl2Points i
      (Matrix.SpecialLinearGroup.diag2 (t : K) t.ne_zero) *
        (G.weylPoint w)⁻¹ ∈ G.torusPoints
  rw [G.simpleSl2Points_diagonal]
  exact (Subgroup.mem_normalizer_iff.mp (G.weylPoint_mem_normalizer w)
    (Coroot.simpleCorootPoint G i t)).mp (rootCurve_coroot_mem G i t)

/-- The rank-one diagonal fixes every rational Weyl flag. -/
theorem rootSl2Points_diagonal_fixes (w : G.weylGroup) (i : G.rootBase.support)
    (t : Kˣ) (x : G.weylGroup) :
    rootSl2Points G w i (Matrix.SpecialLinearGroup.diag2 (t : K) t.ne_zero) •
        flagProjection G (G.weylPoint x) = flagProjection G (G.weylPoint x) :=
  rootCurve_torus_fixes G _ (rootSl2Points_diagonal_mem G w i t) x

private theorem inverse_rootSpace (x : G.weylGroup) (r : G.rootIndex) :
    (G.rootWeightSpace r).map
        (affineGroupAdjointLieEquiv (G.weylPoint x)⁻¹).toLinearEquiv.toLinearMap =
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm x⁻¹ r) := by
  have he : G.rootSystem.weylGroupToPerm x
      (G.rootSystem.weylGroupToPerm x⁻¹ r) = r := by
    change (G.rootSystem.weylGroupToPerm x *
      G.rootSystem.weylGroupToPerm x⁻¹) r = r
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hforward := G.weylPoint_rootWeightSpace x
    (G.rootSystem.weylGroupToPerm x⁻¹ r)
  rw [he] at hforward
  apply rootCurve_map_inverse _ _ _ _ hforward
  apply LinearMap.ext
  intro d
  change affineGroupAdjointRepresentation (G.weylPoint x)⁻¹
    (affineGroupAdjointRepresentation (G.weylPoint x) d) = d
  rw [← Module.End.mul_apply, ← map_mul]
  simp

/-- A root parameter fixes a Weyl flag when its inverse Weyl transform is positive. -/
theorem rootCurve_upper_fixes (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (r : G.rootIndex) (hφ : gaAffineGroupTangent φ ∈ G.rootWeightSpace r)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹ r)) (t : K) :
    gaParameterPoint φ t • flagProjection G (G.weylPoint x) =
      flagProjection G (G.weylPoint x) := by
  apply rootCurve_coset_fixed G.borelPoints (G.weylPoint x) (gaParameterPoint φ t)
  have htangent : gaAffineGroupTangent
      (φ.comp (affineGroupConjugationBialgHom (G.weylPoint x)⁻¹)) ∈
        hopfTangentImage G.borelIdeal := by
    rw [gaTangent_comp_conjugation]
    have hm : affineGroupAdjointLieEquiv (G.weylPoint x)⁻¹ (gaAffineGroupTangent φ) ∈
        (G.rootWeightSpace r).map
          (affineGroupAdjointLieEquiv (G.weylPoint x)⁻¹).toLinearEquiv.toLinearMap :=
      Submodule.mem_map.mpr ⟨_, hφ, rfl⟩
    rw [inverse_rootSpace G x r] at hm
    exact (G.rootWeightSpace_le_borel _).mpr hpos hm
  have hp := GaParameterPoint.mem_of_tangent_mem_quotient
    (φ.comp (affineGroupConjugationBialgHom (G.weylPoint x)⁻¹))
    G.borelIdeal htangent t
  have he := gaPoints_comp_conjugation φ (G.weylPoint x)⁻¹ (Multiplicative.ofAdd t)
  change gaParameterPoint _ t =
    (G.weylPoint x)⁻¹ * gaParameterPoint φ t * ((G.weylPoint x)⁻¹)⁻¹ at he
  exact conjugate_mem G.borelPoints (G.weylPoint x) (gaParameterPoint φ t) hp he rfl

/-- The specified upper chart parameter has the required stabilizer equation. -/
theorem rootUpperMap_fixes (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) (t : K) :
    gaParameterPoint (rootUpperMap G w i) t • flagProjection G (G.weylPoint x) =
      flagProjection G (G.weylPoint x) :=
  rootCurve_upper_fixes G _ _ (rootUpperMap_tangent G w i) x hpos t

end SchubertGeometry
