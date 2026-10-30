import OrbitComplexity.GroupActions.Rosenlicht.OpenInvariants
import OrbitComplexity.GroupActions.Rosenlicht.OrbitMaximum

/-!
# Complexity on equivariant dense opens

An equivariant dominant open immersion identifies invariant rational functions.
The transcendence-degree formula therefore preserves minimum orbit codimension.
In particular, two varieties with a common equivariant dense open have equal
minimum orbit codimension.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X Y : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]
variable [IrreducibleSpace Y.scheme]

/-- An equivariant dominant open immersion preserves minimum orbit codimension. -/
theorem minOrbitCodim_eq_of_openImmersion (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] [IsOpenImmersion f.left] [IsDominant f.left] :
    minOrbitCodim H X = minOrbitCodim H Y := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  rw [minOrbitCodim_eq_trdeg H X, minOrbitCodim_eq_trdeg H Y]
  simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat
    (invariantFieldOpenEquiv H X Y f).symm.lift_trdeg_eq

/-- Varieties with a common equivariant dense open have equal minimum orbit codimension. -/
theorem minOrbitCodim_eq_of_commonOpen (U : GroupActions.Variety K)
    [ModObj H.toOver U.toOver] [IrreducibleSpace U.scheme]
    (f : U.toOver ⟶ X.toOver) (g : U.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] [IsModHom H.toOver g]
    [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    [IsDominant f.left] [IsDominant g.left] : minOrbitCodim H X = minOrbitCodim H Y :=
  (minOrbitCodim_eq_of_openImmersion H U X f).symm.trans
    (minOrbitCodim_eq_of_openImmersion H U Y g)

end

end GroupActions.Variety
