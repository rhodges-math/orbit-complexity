import OrbitComplexity.GroupActions.Rosenlicht.OrbitSeparators
import OrbitComplexity.GroupActions.Rosenlicht.InvariantCoordinateValues
import OrbitComplexity.GroupActions.Rosenlicht.FractionValues

/-!
# Generic fibres of the invariant map

Finite invariant orbit separators factor through the coordinate algebra of the invariant-
field model after restricting to a nonempty open subset.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- Fibres of the invariant morphism separate orbits on a nonempty open subset
of its domain. -/
theorem exists_open_invariantMap_fibres :
    ∃ W : X.scheme.Opens, (W : Set X.scheme).Nonempty ∧
      ∃ hWD : W ≤ (invariantMap H X).domain,
        ∀ (x y : X.points) (hx : X.pointMap x ∈ W) (hy : X.pointMap y ∈ W),
          (invariantMorphism H X).left ⟨X.pointMap x, hWD hx⟩ =
            (invariantMorphism H X).left ⟨X.pointMap y, hWD hy⟩ →
              y ∈ MulAction.orbit H.points x := by
  classical
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  obtain ⟨U, hUa, hU, S, hS, W₁, hW₁, hWU, hsep⟩ :=
    exists_open_orbit_separators H X
  have : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
  let D := (invariantMap H X).domain
  have : Nonempty D := Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  have hηD : genericPoint X.scheme ∈ D :=
    ((genericPoint_spec X.scheme).mem_open_set_iff D.isOpen).mpr
      (by simpa using invariantDomain_nonempty H X)
  have hηW₁ : genericPoint X.scheme ∈ W₁ :=
    ((genericPoint_spec X.scheme).mem_open_set_iff W₁.isOpen).mpr (by simpa using hW₁)
  obtain ⟨V, hVa, hV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X.scheme ∈ U ⊓ D ⊓ W₁ from ⟨⟨hU, hηD⟩, hηW₁⟩)
  have : Nonempty V := ⟨⟨genericPoint X.scheme, hV⟩⟩
  have eU : V ≤ U := hVle.trans (inf_le_left.trans inf_le_left)
  have eD : V ≤ D := hVle.trans (inf_le_left.trans inf_le_right)
  have eW : V ≤ W₁ := hVle.trans inf_le_right
  let R := Γ(X.scheme, V)
  let F := X.scheme.functionField
  let E := invariantField H X
  let A := fieldModelAlgebra K E
  let j : R →+* F := (X.scheme.germToFunctionField V).hom
  let ρ : Γ(X.scheme, U) →+* R := (X.scheme.presheaf.map (homOfLE eU).op).hom
  let ψD : A →+* Γ(X.scheme, D) := invariantCoordinates H X
  let ψ : A →+* R := (X.scheme.presheaf.map (homOfLE eD).op).hom.comp ψD
  let φ : A →+* F := (E.val.comp A.val).toRingHom
  have hφ : Function.Injective φ := E.val.injective.comp Subtype.val_injective
  have hj : Function.Injective j := X.scheme.germToFunctionField_injective V
  have hψ : j.comp ψ = φ := by
    ext a
    change X.scheme.presheaf.germ V (genericPoint X.scheme) _
      (X.scheme.presheaf.map (homOfLE eD).op (ψD a)) = a.val.val
    rw [X.scheme.presheaf.germ_res_apply]
    exact invariantCoordinate_germ H X a
  have hρ (a : Γ(X.scheme, U)) : j (ρ a) = X.scheme.germToFunctionField U a := by
    change X.scheme.presheaf.germ V (genericPoint X.scheme) _
      (X.scheme.presheaf.map (homOfLE eU).op a) = _
    rw [X.scheme.presheaf.germ_res_apply]
  let T := S.image ρ
  have hT : ∀ a ∈ T, ∃ n b : A, φ b ≠ 0 ∧ j a = φ n / φ b := by
    intro a ha
    change a ∈ S.image ρ at ha
    obtain ⟨a₀, ha₀, hza⟩ := Finset.mem_image.mp ha
    subst a
    let z : E := ⟨X.scheme.germToFunctionField U a₀, hS a₀ ha₀⟩
    obtain ⟨n, b, hb, he⟩ := IsFractionRing.div_surjective A z
    refine ⟨n, b, map_ne_zero_of_mem_nonZeroDivisors φ hφ hb, ?_⟩
    rw [hρ]
    exact (congrArg (fun z : E ↦ z.val) he).symm
  obtain ⟨d, hd, htest⟩ := exists_fraction_value_tests R F A j hj φ ψ hψ T hT
  have hηd : genericPoint X.scheme ∈ X.scheme.basicOpen d := by
    rw [Scheme.mem_basicOpen X.scheme d (genericPoint X.scheme) hV, isUnit_iff_ne_zero]
    intro hz
    apply hd
    apply hj
    simpa only [map_zero] using hz
  let W := V ⊓ X.scheme.basicOpen d
  have hηW : genericPoint X.scheme ∈ W := ⟨hV, hηd⟩
  have hWD : W ≤ D := inf_le_left.trans eD
  refine ⟨W, ⟨genericPoint X.scheme, hηW⟩, hWD, ?_⟩
  intro x y hx hy hxy
  let px := pointInOpen X V x hx.1
  let py := pointInOpen X V y hy.1
  let qx := pointInOpen X D x (hWD hx)
  let qy := pointInOpen X D y (hWD hy)
  let fx : R →+* K := affineOpenPointEval X V hVa px
  let fy : R →+* K := affineOpenPointEval X V hVa py
  let px' : Spec (.of K) ⟶ V.toScheme := px.val
  let py' : Spec (.of K) ⟶ V.toScheme := py.val
  let qx' : Spec (.of K) ⟶ D.toScheme := qx.val
  let qy' : Spec (.of K) ⟶ D.toScheme := qy.val
  have hpx : px' ≫ X.scheme.homOfLE eD = qx' := by
    apply (cancel_mono D.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact (congrArg Subtype.val (mapPoints_pointInOpen X V x hx.1)).trans
      (congrArg Subtype.val (mapPoints_pointInOpen X D x (hWD hx))).symm
  have hpy : py' ≫ X.scheme.homOfLE eD = qy' := by
    apply (cancel_mono D.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact (congrArg Subtype.val (mapPoints_pointInOpen X V y hy.1)).trans
      (congrArg Subtype.val (mapPoints_pointInOpen X D y (hWD hy))).symm
  have hcoord : fx.comp ψ = fy.comp ψ := by
    have he := invariantCoordinates_values H X x y (hWD hx) (hWD hy) hxy
    ext a
    change affineOpenPointEval X V hVa px
        (X.scheme.presheaf.map (homOfLE eD).op (ψD a)) =
      affineOpenPointEval X V hVa py
        (X.scheme.presheaf.map (homOfLE eD).op (ψD a))
    rw [affineOpenPointEval_eq_open, affineOpenPointEval_eq_open,
      openPointEval_res X D V eD px qx hpx,
      openPointEval_res X D V eD py qy hpy]
    exact congrArg (fun f : A →+* K ↦ f a) he
  have hunit : IsUnit (fx d) := by
    apply affineOpenPointEval_isUnit X V hVa px d
    rw [mapPoints_pointInOpen]
    exact hx.2
  have hvalues := htest K fx fy hunit hcoord
  apply hsep x y (eW hx.1) (eW hy.1)
  intro a ha
  have heq := hvalues (ρ a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  exact (regularValue_res X U V hUa hVa eU x hx.1 a).symm.trans
    (heq.trans (regularValue_res X U V hUa hVa eU y hy.1 a))

end

end GroupActions.Variety
