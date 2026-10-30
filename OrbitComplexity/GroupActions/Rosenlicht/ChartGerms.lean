import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields

/-!
# Regular sections under function-field pullback
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

/-- Function-field pullback of a regular section agrees with its pullback to
any nonempty open subset mapping into that section's domain. -/
theorem functionFieldMap_appLE {Z X : Scheme.{u}}
    [IrreducibleSpace Z] [IrreducibleSpace X] (p : Z ⟶ X) [IsDominant p]
    (U : X.Opens) [Nonempty U] (V : Z.Opens) [Nonempty V]
    (e : V ≤ p ⁻¹ᵁ U) (s : Γ(X, U)) :
    functionFieldMap p (X.germToFunctionField U s) =
      Z.germToFunctionField V (p.appLE U V e s) := by
  have : Nonempty (p ⁻¹ᵁ U) := by
    obtain ⟨z⟩ := (inferInstance : Nonempty V)
    exact ⟨⟨z.val, e z.property⟩⟩
  rw [functionFieldMap_germ]
  change Z.presheaf.germ (p ⁻¹ᵁ U) (genericPoint Z) _ (p.app U s) =
    Z.presheaf.germ V (genericPoint Z) _
      (Z.presheaf.map (homOfLE e).op (p.app U s))
  rw [Z.presheaf.germ_res_apply]

/-- Restriction to an open subscheme takes a rational germ to the germ of
the corresponding global section on that open subscheme. -/
theorem openFunctionFieldMap_germ {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (s : Γ(X, U)) :
    letI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    letI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (by
      obtain ⟨x⟩ := (inferInstance : Nonempty U)
      exact ⟨x.val, x.property⟩))
    functionFieldMap U.ι (X.germToFunctionField U s) =
      U.toScheme.germToFunctionField ⊤ (U.topIso.inv s) := by
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.val, x.property⟩))
  have : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  rw [functionFieldMap_appLE U.ι U ⊤ U.ι_preimage_self.ge]
  congr 1
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

end

end GroupActions
