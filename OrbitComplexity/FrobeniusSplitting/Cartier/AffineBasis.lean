import OrbitComplexity.FrobeniusSplitting.Modules.Polynomial
import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius
import OrbitComplexity.FrobeniusSplitting.Modules.Sections

/-! # Residue-monomial coordinates for the Frobenius module on the affine line -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace FrobeniusSplitting.AffineCartier

variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p]

private abbrev polynomialRing := CommRingCat.of (Polynomial C)
private abbrev affineLine := Spec (polynomialRing C)
private abbrev residueIndex := ULift.{u} (Fin p)

private def frobeniusModule : (affineLine C).Modules :=
  frobeniusRestriction C p
    (Spec.map (CommRingCat.ofHom (Polynomial.C : C →+* Polynomial C)))
    (SheafOfModules.unit (affineLine C).ringCatSheaf)

private instance frobeniusModule_qc : (frobeniusModule C p).IsQuasicoherent := by
  let M : (affineLine C).Modules := SheafOfModules.unit (affineLine C).ringCatSheaf
  let : M.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr inferInstance
  exact frobeniusAffine_isQuasicoherent C p _ M

private def polynomialModule : ModuleCat (polynomialRing C) :=
  letI := polynomialAbsoluteModule C p
  ModuleCat.of (Polynomial C) (Polynomial C)

private def polynomialGammaIso : polynomialModule C p ≅
    moduleSpecΓFunctor.obj (frobeniusModule C p) := by
  refine LinearEquiv.toModuleIso
    (X₁ := polynomialModule C p)
    (X₂ := moduleSpecΓFunctor.obj (frobeniusModule C p))
    (m₁ := (polynomialModule C p).isModule)
    (m₂ := (moduleSpecΓFunctor.obj (frobeniusModule C p)).isModule)
    { __ := (Scheme.ΓSpecIso (polynomialRing C)).symm.commRingCatIsoToRingEquiv.toAddEquiv
      map_smul' := ?_ }
  intro r m
  change (Scheme.ΓSpecIso (polynomialRing C)).inv
      ((show Polynomial C from r) ^ p * (show Polynomial C from m)) =
    ((Scheme.ΓSpecIso (polynomialRing C)).inv (show Polynomial C from r)) ^ p *
      (Scheme.ΓSpecIso (polynomialRing C)).inv (show Polynomial C from m)
  rw [map_mul, map_pow]

private def residuePolynomialIso :
    ModuleCat.of (polynomialRing C) (Fin p → Polynomial C) ≅ polynomialModule C p :=
  (polynomialAbsoluteEval C p).toModuleIso

private def residueCoordinates :
    (residueIndex p →₀ Polynomial C) ≃ₗ[Polynomial C] (Fin p → Polynomial C) :=
  (Finsupp.linearEquivFunOnFinite (Polynomial C) (Polynomial C) (residueIndex p)).trans
    { toFun := fun v i => v ⟨i⟩
      invFun := fun v i => v i.down
      left_inv := fun v => by funext i; cases i; rfl
      right_inv := fun v => rfl
      map_add' := fun v w => rfl
      map_smul' := fun r v => rfl }

private def freeGammaIso :
    ModuleCat.of (polynomialRing C) (residueIndex p →₀ Polynomial C) ≅
      moduleSpecΓFunctor.obj
        (SheafOfModules.free (R := (affineLine C).ringCatSheaf) (residueIndex p)) :=
  tilde.isoTop (ModuleCat.of (polynomialRing C) (residueIndex p →₀ Polynomial C)) ≪≫
    moduleSpecΓFunctor.mapIso (tildeFinsupp (residueIndex p))

private def basisGammaIso :
    moduleSpecΓFunctor.obj
        (SheafOfModules.free (R := (affineLine C).ringCatSheaf) (residueIndex p)) ≅
      moduleSpecΓFunctor.obj (frobeniusModule C p) :=
  (freeGammaIso C p).symm ≪≫ (residueCoordinates C p).toModuleIso ≪≫
    residuePolynomialIso C p ≪≫ polynomialGammaIso C p

private theorem gamma_counit_inv {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)] :
    (moduleSpecΓFunctor (R := R)).map (inv (Scheme.Modules.fromTildeΓ (R := R) M)) =
      (tilde.isoTop ((moduleSpecΓFunctor (R := R)).obj M)).hom := by
  let G := moduleSpecΓFunctor (R := R)
  let e := Scheme.Modules.fromTildeΓ (R := R) M
  have hl : G.map (inv e) ≫ G.map e = 𝟙 (G.obj M) :=
    (G.map_comp (inv e) e).symm.trans
      ((congrArg (fun k : M ⟶ M => G.map k) (IsIso.inv_hom_id e)).trans (G.map_id M))
  have hr : (tilde.isoTop (G.obj M)).hom ≫ G.map e = 𝟙 (G.obj M) :=
    (tilde.adjunction (R := R)).right_triangle_components M
  exact (cancel_mono (G.map e)).mp (hl.trans hr.symm)

private theorem gamma_lift {R : CommRingCat.{u}} (M N : (Spec R).Modules)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    (f : (moduleSpecΓFunctor (R := R)).obj M ⟶
      (moduleSpecΓFunctor (R := R)).obj N) :
    (moduleSpecΓFunctor (R := R)).map
        (inv (Scheme.Modules.fromTildeΓ (R := R) M) ≫
          (tilde.functor R).map f ≫ Scheme.Modules.fromTildeΓ (R := R) N) = f := by
  let G := moduleSpecΓFunctor (R := R)
  let F := tilde.functor R
  let eM := Scheme.Modules.fromTildeΓ (R := R) M
  let eN := Scheme.Modules.fromTildeΓ (R := R) N
  let aM := (tilde.isoTop (G.obj M)).hom
  let aN := (tilde.isoTop (G.obj N)).hom
  have hi : G.map (inv eM) = aM := gamma_counit_inv M
  have hn : f ≫ aN = aM ≫ G.map (F.map f) :=
    (tilde.toTildeΓNatIso (R := R)).hom.naturality f
  have ht : aN ≫ G.map eN = 𝟙 (G.obj N) :=
    (tilde.adjunction (R := R)).right_triangle_components N
  calc
    G.map (inv eM ≫ F.map f ≫ eN) =
        G.map (inv eM) ≫ G.map (F.map f ≫ eN) := G.map_comp _ _
    _ = G.map (inv eM) ≫ (G.map (F.map f) ≫ G.map eN) :=
      congrArg (fun k : G.obj (F.obj (G.obj M)) ⟶ G.obj N => G.map (inv eM) ≫ k)
        (G.map_comp _ _)
    _ = aM ≫ (G.map (F.map f) ≫ G.map eN) :=
      congrArg (fun k : G.obj M ⟶ G.obj (F.obj (G.obj M)) =>
        k ≫ (G.map (F.map f) ≫ G.map eN)) hi
    _ = (aM ≫ G.map (F.map f)) ≫ G.map eN := (Category.assoc _ _ _).symm
    _ = (f ≫ aN) ≫ G.map eN :=
      congrArg (fun k : G.obj M ⟶ G.obj (F.obj (G.obj N)) => k ≫ G.map eN) hn.symm
    _ = f ≫ (aN ≫ G.map eN) := Category.assoc _ _ _
    _ = f ≫ 𝟙 (G.obj N) := congrArg (fun k : G.obj N ⟶ G.obj N => f ≫ k) ht
    _ = f := Category.comp_id _

/-- The p residue monomials give a free module-sheaf model for the Frobenius source. -/
def affineFrobeniusBasisIso :
    (SheafOfModules.free (R := (affineLine C).ringCatSheaf) (residueIndex p) :
      (affineLine C).Modules) ≅ frobeniusModule C p :=
  (asIso (Scheme.Modules.fromTildeΓ (R := polynomialRing C)
    (SheafOfModules.free (R := (affineLine C).ringCatSheaf) (residueIndex p)))).symm ≪≫
      (tilde.functor (polynomialRing C)).mapIso (basisGammaIso C p) ≪≫
      (by
        have h : IsIso (Scheme.Modules.fromTildeΓ
            (R := polynomialRing C) (frobeniusModule C p)) :=
          (isQuasicoherent_iff_isIso_fromTildeΓ
            (R := polynomialRing C) (frobeniusModule C p)).mp (frobeniusModule_qc C p)
        exact @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ
          (R := polynomialRing C) (frobeniusModule C p)) h)

private theorem affineFrobeniusBasisIso_gamma :
    (moduleSpecΓFunctor (R := polynomialRing C)).map (affineFrobeniusBasisIso C p).hom =
      (basisGammaIso C p).hom :=
  gamma_lift _ _ (basisGammaIso C p).hom

private theorem tilde_single (R : CommRingCat.{u}) (I : Type u) (i : I) :
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
        (tildeFinsupp (R := R) I).hom =
      (tildeSelf (R := R)).hom ≫ SheafOfModules.ιFree i := by
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R I)) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor fun (_ : I) => ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) :=
    Discrete.natIso (fun _ => tildeSelf)
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H)
    (coproductIsCoproduct (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf))
    (Discrete.mk i)
  change tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
    (tildeFinsupp (R := R) I).hom = SheafOfModules.ιFree i at h
  exact h

omit [ExpChar C p] [PerfectRing C p] in
private theorem freeGammaIso_single (i : residueIndex p) (r : polynomialRing C) :
    (freeGammaIso C p).hom (Finsupp.single i r) =
      (moduleSpecΓFunctor.map (SheafOfModules.ιFree i)).hom
        ((Scheme.ΓSpecIso (polynomialRing C)).inv r) := by
  let R := polynomialRing C
  let I := residueIndex p
  have hn := congrArg (fun f => f r)
    ((tilde.toTildeΓNatIso (R := R)).hom.naturality
      (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))))
  change (tilde.isoTop (ModuleCat.of R (I →₀ R))).hom (Finsupp.single i r) =
    (moduleSpecΓFunctor.map
      (tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))))).hom
      ((tilde.isoTop (ModuleCat.of R R)).hom r) at hn
  change (moduleSpecΓFunctor.map (tildeFinsupp (R := R) I).hom).hom
    ((tilde.isoTop (ModuleCat.of R (I →₀ R))).hom (Finsupp.single i r)) = _
  rw [hn]
  change (moduleSpecΓFunctor.map
    (tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
      (tildeFinsupp (R := R) I).hom)).hom
      ((tilde.isoTop (ModuleCat.of R R)).hom r) = _
  rw [tilde_single]
  rfl

private theorem basisGammaIso_generator (i : Fin p) :
    (basisGammaIso C p).hom
        (((moduleSpecΓFunctor (R := polynomialRing C)).map
          (SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf)
            (I := residueIndex p) (ULift.up i))).hom
          ((Scheme.ΓSpecIso (polynomialRing C)).inv 1)) =
      (Scheme.ΓSpecIso (polynomialRing C)).inv ((Polynomial.X : Polynomial C) ^ (i : ℕ)) := by
  classical
  have hi := freeGammaIso_single C p (ULift.up i) 1
  have he : (freeGammaIso C p).inv
      (((moduleSpecΓFunctor (R := polynomialRing C)).map
          (SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf)
            (I := residueIndex p) (ULift.up i))).hom
        ((Scheme.ΓSpecIso (polynomialRing C)).inv 1)) = Finsupp.single (ULift.up i) 1 := by
    rw [← hi]
    exact congrArg
      (fun f : ModuleCat.of (polynomialRing C) (residueIndex p →₀ Polynomial C) ⟶
          ModuleCat.of (polynomialRing C) (residueIndex p →₀ Polynomial C) =>
        f.hom (Finsupp.single (ULift.up i) 1)) (freeGammaIso C p).hom_inv_id
  change (Scheme.ΓSpecIso (polynomialRing C)).inv
      (polynomialAbsoluteEval C p (residueCoordinates C p ((freeGammaIso C p).inv _))) = _
  rw [he, polynomialAbsoluteEval_apply]
  congr 1
  change (∑ j : Fin p,
    (Finsupp.single (ULift.up i) (1 : Polynomial C) (ULift.up j)) ^ p *
      Polynomial.X ^ (j : ℕ)) = Polynomial.X ^ (i : ℕ)
  simp [Finsupp.single_apply, expChar_ne_zero C p]

private theorem affineFrobeniusBasisIso_top (i : Fin p) :
    (((SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf) (ULift.up i)) ≫
      (affineFrobeniusBasisIso C p).hom).val.app (.op ⊤)).hom (1 : Γ(affineLine C, ⊤)) =
        (Scheme.ΓSpecIso (polynomialRing C)).inv ((Polynomial.X : Polynomial C) ^ (i : ℕ)) := by
  have h := congrArg
    (fun f => f (((moduleSpecΓFunctor (R := polynomialRing C)).map
      (SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf)
        (I := residueIndex p) (ULift.up i))).hom
      ((Scheme.ΓSpecIso (polynomialRing C)).inv 1)))
    (affineFrobeniusBasisIso_gamma C p)
  have he := h.trans (basisGammaIso_generator C p i)
  change (((affineFrobeniusBasisIso C p).hom.val.app (.op ⊤)).hom
      (((SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf)
        (I := residueIndex p) (ULift.up i)).val.app (.op ⊤)).hom
        ((Scheme.ΓSpecIso (polynomialRing C)).inv 1))) = _ at he
  rw [map_one] at he
  exact he

/-- On each open, the free generator maps to the restricted residue monomial. -/
theorem affineFrobeniusBasisIso_generator (U : (affineLine C).Opens) (i : Fin p) :
    (((SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf) (ULift.up i)) ≫
      (affineFrobeniusBasisIso C p).hom).val.app (.op U)).hom (1 : Γ(affineLine C, U)) =
        ((Scheme.ΓSpecIso (polynomialRing C)).inv ≫
          (affineLine C).presheaf.map U.leTop.op) ((Polynomial.X : Polynomial C) ^ (i : ℕ)) := by
  let t := (SheafOfModules.ιFree (R := (affineLine C).ringCatSheaf) (ULift.up i)) ≫
    (affineFrobeniusBasisIso C p).hom
  have hn := congrArg (fun f => f (1 : Γ(affineLine C, ⊤)))
    (t.val.naturality U.leTop.op)
  change ((t.val.app (.op U)).hom
      ((affineLine C).presheaf.map U.leTop.op 1)) =
    (affineLine C).presheaf.map U.leTop.op
      ((t.val.app (.op ⊤)).hom (1 : Γ(affineLine C, ⊤))) at hn
  rw [map_one, affineFrobeniusBasisIso_top] at hn
  exact hn

end FrobeniusSplitting.AffineCartier
