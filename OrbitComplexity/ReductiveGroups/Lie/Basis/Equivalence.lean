/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import OrbitComplexity.ReductiveGroups.Lie.Cartan.IdealDetection
import Mathlib.Algebra.Lie.Basis.Basic
import Mathlib.Algebra.Lie.Prod

/-! # Equivalences from bases of split Killing Lie algebras

The paired-generator construction and its Cartan comparison follow the
proof in `Mathlib.Algebra.Lie.Basis.Prod`. Cartan detection of ideals permits
the projection argument for split Killing algebras.
-/

noncomputable section

namespace ReductiveGroups.LieBasis

open Function LieAlgebra LieSubalgebra Set Submodule

variable {ι₁ ι₂ L₁ L₂ : Type*} [Finite ι₁] [Finite ι₂] (eι : ι₁ ≃ ι₂)
  [LieRing L₁] [LieRing L₂]

section CommRing

variable {R : Type*} [CommRing R]
  [LieAlgebra R L₁] {H₁ : LieSubalgebra R L₁} (b₁ : Basis ι₁ H₁)
  [LieAlgebra R L₂] {H₂ : LieSubalgebra R L₂} (b₂ : Basis ι₂ H₂)

/-- A distinguished subalgebra of the product of two based Lie algebras with equivalent indexing
sets. -/
private def prod :
    LieSubalgebra R (L₁ × L₂) :=
  .lieSpan _ _ <|
    {(b₁.h i, b₂.h (eι i)) | i : ι₁} ∪
    {(b₁.e i, b₂.e (eι i)) | i : ι₁} ∪
    {(b₁.f i, b₂.f (eι i)) | i : ι₁}

/-- Interchanging the two based algebras identifies the paired-generator subalgebras. -/
private def prodSymmEquiv : prod eι.symm b₂ b₁ ≃ₗ⁅R⁆ (prod eι b₁ b₂) :=
  have : (prod eι.symm b₂ b₁).map (LieEquiv.prodComm R L₂ L₁) = (prod eι b₁ b₂) := by
    rw [prod, prod, map_lieSpan]; congr; ext; aesop
  (LieEquiv.lieSubalgebraMap (prod eι.symm b₂ b₁) (LieEquiv.prodComm _ _ _)).trans
    (LieEquiv.ofEq _ _ <| by simpa)

@[simp]
private lemma prodSymmEquiv_symm_apply {y : (prod eι b₁ b₂)} :
    (prodSymmEquiv eι b₁ b₂).symm y =
      ⟨((y : L₁ × L₂).snd, (y : L₁ × L₂).fst), ((prodSymmEquiv eι b₁ b₂).symm y).property⟩ :=
  rfl

private lemma h_mem_prod (i : ι₁) :
    (b₁.h i, b₂.h (eι i)) ∈ (prod eι b₁ b₂) :=
  subset_lieSpan <| by aesop

/-- A distinguished subalgebra of the Lie algebra defined by `ReductiveGroups.LieBasis.prod`.

The assumptions of `LieAlgebra.Basis.isCartanSubalgebra` make this a Cartan subalgebra
of `ReductiveGroups.LieBasis.prod`. -/
private def prodCartan :
    LieSubalgebra R (prod eι b₁ b₂) :=
  .lieSpan _ _ {⟨(b₁.h i, b₂.h (eι i)), h_mem_prod eι b₁ b₂ i⟩ | i : ι₁}

open Finsupp in
private lemma prodCartanEquiv_aux :
    InjOn (LinearMap.fst R L₁ L₂) (span R {(b₁.h i, b₂.h (eι i)) | i : ι₁}) := by
  suffices ∀ y, (∃ l : ι₁ →₀ R,
      (l.linearCombination R fun i ↦ (b₁.h i, b₂.h (eι i))) = (0, y)) → y = 0 by
    have aux : {(b₁.h i, b₂.h (eι i)) | i : ι₁} = (fun i : ι₁ ↦ (b₁.h i, b₂.h (eι i))) '' univ := by
      ext; simp
    simp_rw [← LinearMap.disjoint_ker_iff_injOn, LinearMap.disjoint_ker, aux,
      mem_span_image_iff_linearCombination]
    aesop
  intro y ⟨f, hf⟩
  suffices linearCombination R b₁.h f = 0 by
    rw [LinearMap.map_eq_zero_iff _ b₁.linInd] at this
    aesop (add simp Prod.ext_iff)
  replace hf := (LinearMap.fst R L₁ L₂).congr_arg hf
  rw [← LinearMap.comp_apply, ← Finsupp.linearCombination_linear_comp] at hf
  aesop

open LinearMap in
/-- The paired-generator Lie algebra has a Cartan subalgebra isomorphic
to the Cartan subalgebra of the input. -/
private def prodCartanEquiv :
    prodCartan eι b₁ b₂ ≃ₗ[R] H₁ :=
  /- Informally this is obvious since `prodCartan eι b₁ b₂` is the linear span of
  `{(b₁.h i, b₂.h (eι i)) | i : ι₁}` and `H₁` is the linear span of `{b₁.h i | i : ι₁}` (and both
  families are linearly independent) but formally some care is required. -/
  have h₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl =
      (lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} : Set (L₁ × L₂)) := by
    rw [prodCartan, map_lieSpan]; congr; aesop
  have h₂ : (lieSpan R _ {(b₁.h i, b₂.h (eι i)) | i : ι₁}) =
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} :=
    coe_lieSpan_eq_span_of_forall_lie_eq_zero <| by simp [b₁.lie_h_h, b₂.lie_h_h]
  have h₃ : (span R {(b₁.h i, b₂.h (eι i)) | i : ι₁}).map (.fst R L₁ L₂) = span R (range b₁.h) := by
    rw [Submodule.map_span]; congr; ext; simp
  have h₄ : lieSpan R L₁ (range b₁.h) = span R (range b₁.h) := by
    rw [← b₁.coe_cartan_eq_span, toSubmodule_inj, ← b₁.cartan_eq_lieSpan]
  have h₅ : (H₁ : Set L₁) = lieSpan R L₁ (range b₁.h) := by simp [b₁.cartan_eq_lieSpan]
  let e₀ : prodCartan eι b₁ b₂ ≃ₗ[R] (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl :=
    (prodCartan eι b₁ b₂).equivMapOfInjective (prod eι b₁ b₂).incl <| by simp
  let e₁ : (prodCartan eι b₁ b₂).map (prod eι b₁ b₂).incl ≃ₗ[R]
      lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LieEquiv.ofEq _ _ h₁
  let e₂ : lieSpan R (L₁ × L₂) {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R]
      span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} := LinearEquiv.ofEq _ _ h₂
  let e₃ : span R {(b₁.h i, b₂.h (eι i)) | i : ι₁} ≃ₗ[R] span R (range b₁.h) :=
    (LinearEquiv.ofBijective _ ⟨submoduleMap_injective_of_injOn (prodCartanEquiv_aux eι b₁ b₂),
      submoduleMap_surjective _ _⟩).trans <| .ofEq _ _ h₃
  let e₄ : span R (range b₁.h) ≃ₗ[R] lieSpan R L₁ (range b₁.h) := LinearEquiv.ofEq _ _ h₄.symm
  let e₅ : lieSpan R L₁ (range b₁.h) ≃ₗ[R] H₁ := (LieEquiv.ofEq _ _ h₅).symm
  e₀.trans <| e₁.trans <| e₂.trans <| e₃.trans <| e₄.trans e₅

private abbrev prodH (i : ι₁) : (prod eι b₁ b₂) :=
  ⟨(b₁.h i, b₂.h (eι i)), subset_lieSpan <| by aesop⟩

private abbrev prodE (i : ι₁) : (prod eι b₁ b₂) :=
  ⟨(b₁.e i, b₂.e (eι i)), subset_lieSpan <| by aesop⟩

private abbrev prodF (i : ι₁) : (prod eι b₁ b₂) :=
  ⟨(b₁.f i, b₂.f (eι i)), subset_lieSpan <| by aesop⟩

private lemma basisProd_aux :
    lieSpan R (prod eι b₁ b₂) (range (prodE eι b₁ b₂) ∪ range (prodF eι b₁ b₂)) = ⊤ := by
  suffices lieSpan R (prod eι b₁ b₂) (range (prodE eι b₁ b₂) ∪ range (prodF eι b₁ b₂)) =
      lieSpan R (prod eι b₁ b₂)
        (range (prodH eι b₁ b₂) ∪ range (prodE eι b₁ b₂) ∪ range (prodF eι b₁ b₂)) by
    have hr : range (prodH eι b₁ b₂) ∪ range (prodE eι b₁ b₂) ∪ range (prodF eι b₁ b₂) =
        Subtype.val ⁻¹' ( {(b₁.h i, b₂.h (eι i)) | i : ι₁} ∪
                          {(b₁.e i, b₂.e (eι i)) | i : ι₁} ∪
                          {(b₁.f i, b₂.f (eι i)) | i : ι₁} ) := by
      ext; simp [Subtype.ext_iff]
    rw [this, hr]
    exact lieSpan_lieSpan_coe_preimage
  simp only [union_assoc]
  refine le_antisymm (lieSpan_mono <| by simp) (lieSpan_le.mpr <| union_subset ?_ subset_lieSpan)
  rintro - ⟨i, rfl⟩
  have hef : prodH eι b₁ b₂ i = ⁅prodE eι b₁ b₂ i, prodF eι b₁ b₂ i⁆ := by
    simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
  rw [hef]
  apply lie_mem
  · exact subset_lieSpan <| mem_union_left _ <| mem_range_self i
  · exact subset_lieSpan <| mem_union_right _ <| mem_range_self i

/-- A distinguished basis carried by `ReductiveGroups.LieBasis.prod`. -/
private def basisProd (hA : b₁.A.reindex eι eι = b₂.A) :
    Basis ι₁ (prodCartan eι b₁ b₂) where
  A := b₁.A
  h := prodH eι b₁ b₂
  e := prodE eι b₁ b₂
  f := prodF eι b₁ b₂
  cartan_eq_lieSpan := rfl
  span_ef := basisProd_aux eι b₁ b₂
  linInd := .of_comp (prod eι b₁ b₂).subtype <| .of_comp (LinearMap.fst R L₁ L₂) b₁.linInd
  nondegen := b₁.nondegen
  sl2 i :=
    { h_ne_zero := by simp [Subtype.ext_iff, (b₁.sl2 i).h_ne_zero]
      lie_e_f := by simp [Subtype.ext_iff, (b₁.sl2 i).lie_e_f, (b₂.sl2 (eι i)).lie_e_f]
      lie_h_e_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_e_nsmul, (b₂.sl2 (eι i)).lie_h_e_nsmul]
      lie_h_f_nsmul := by
        simp [Subtype.ext_iff, (b₁.sl2 i).lie_h_f_nsmul, (b₂.sl2 (eι i)).lie_h_f_nsmul] }
  lie_h_h i j := by simp [Subtype.ext_iff, b₁.lie_h_h, b₂.lie_h_h]
  lie_h_e i j := by simp [Subtype.ext_iff, b₁.lie_h_e, b₂.lie_h_e, ← hA]
  lie_h_f i j := by simp [Subtype.ext_iff, b₁.lie_h_f, b₂.lie_h_f, ← hA]
  lie_e_f_ne i j hij := by
    have hij' : eι i ≠ eι j := by aesop
    simp [Subtype.ext_iff, b₁.lie_e_f_ne i j hij, b₂.lie_e_f_ne _ _ hij']

private lemma surjective_fst_prod :
    Surjective ((LieHom.fst R L₁ L₂).comp (prod eι b₁ b₂).incl) := by
  set L : LieSubalgebra R (L₁ × L₂) := (prod eι b₁ b₂)
  set p₁ : L →ₗ⁅R⁆ L₁ := (LieHom.fst R L₁ L₂).comp L.incl
  have h₁ : range b₁.e = range (p₁ ∘ prodE eι b₁ b₂) := rfl
  have h₂ : range b₁.f = range (p₁ ∘ prodF eι b₁ b₂) := rfl
  rw [← LieHom.range_eq_top, eq_top_iff, ← b₁.span_ef, map_top, ← basisProd_aux eι b₁ b₂,
    map_lieSpan, image_union, h₁, h₂]
  simp [range_comp]

private lemma surjective_snd_prod :
    Surjective ((LieHom.snd R L₁ L₂).comp (prod eι b₁ b₂).incl) := by
  set L : LieSubalgebra R (L₁ × L₂) := (prod eι b₁ b₂)
  set p₂ : L →ₗ⁅R⁆ L₂ := (LieHom.snd R L₁ L₂).comp L.incl
  have h₁ : range b₂.e = range (p₂ ∘ prodE eι b₁ b₂) := by
    simp [show p₂ ∘ prodE eι b₁ b₂ = b₂.e ∘ eι from rfl]
  have h₂ : range b₂.f = range (p₂ ∘ prodF eι b₁ b₂) := by
    simp [show p₂ ∘ prodF eι b₁ b₂ = b₂.f ∘ eι from rfl]
  rw [← LieHom.range_eq_top, eq_top_iff, ← b₂.span_ef, map_top,
    ← basisProd_aux eι b₁ b₂, map_lieSpan, image_union, h₁, h₂]
  simp [range_comp]

private lemma lie_fst_eq_zero_of_mem_prodCartan
    {y : (prod eι b₁ b₂)} (hy : y ∈ prodCartan eι b₁ b₂) (x : H₁) :
    ⁅(y : L₁ × L₂).fst, (x : L₁)⁆ = 0 := by
  have := b₁.isLieAbelian_cartan
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    suffices ⁅b₁.h' i, x⁆ = 0 by simpa [Subtype.ext_iff, Basis.h'] using this
    apply trivial_lie_zero
  | zero => simp
  | add u v hu hv hu' hv' => simp [hu', hv']
  | smul t u hu hu' => simp [hu']
  | lie u v hu hv hu' hv' => simp [hu', hv']

private lemma lie_snd_eq_zero_of_mem_prodCartan
    {y : (prod eι b₁ b₂)} (hy : y ∈ prodCartan eι b₁ b₂) (x : H₂) :
    ⁅(y : L₁ × L₂).snd, (x : L₂)⁆ = 0 := by
  suffices (prodSymmEquiv eι b₁ b₂).symm y ∈ prodCartan eι.symm b₂ b₁ from
    lie_fst_eq_zero_of_mem_prodCartan eι.symm b₂ b₁ this x
  replace hy :
      (prodSymmEquiv eι b₁ b₂).symm y ∈ (prodCartan eι b₁ b₂).map (prodSymmEquiv eι b₁ b₂).symm :=
    mem_image_of_mem (prodSymmEquiv eι b₁ b₂).symm hy
  rw [prodCartan, map_lieSpan] at hy
  rw [prodCartan]
  convert hy
  ext; simp; grind

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]
  [LieAlgebra K L₁] [LieAlgebra K L₂]
  [FiniteDimensional K L₁] [FiniteDimensional K L₂]
  {H₁ : LieSubalgebra K L₁} {H₂ : LieSubalgebra K L₂}
  (b₁ : LieAlgebra.Basis ι₁ H₁) (b₂ : LieAlgebra.Basis ι₂ H₂)
  [LieAlgebra.IsKilling K L₂] [H₂.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H₂ L₂]
  (hA : b₁.A.reindex eι eι = b₂.A)

include hA in
/-- The first projection has no ideal invisible to the paired Cartan. -/
private theorem basisProd_fst_injective :
    Injective ((LieHom.fst K L₁ L₂).comp ((prod eι b₁ b₂)).incl) := by
  let P := (prod eι b₁ b₂)
  let p₁ : P →ₗ⁅K⁆ L₁ := (LieHom.fst K L₁ L₂).comp P.incl
  let p₂ : P →ₗ⁅K⁆ L₂ := (LieHom.snd K L₁ L₂).comp P.incl
  let I : LieIdeal K L₂ := p₁.ker.map p₂
  have hsurj : Surjective p₂ := surjective_snd_prod eι b₁ b₂
  have hI : (I : Set L₂) = p₂ '' p₁.ker :=
    congrArg SetLike.coe (p₁.ker.coe_map_of_surjective hsurj)
  have hinf : I.restr H₂ ⊓ H₂.toLieSubmodule = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    rcases hz with ⟨hzI, hzH⟩
    have hzI' : z ∈ (I : Set L₂) := hzI
    rw [hI] at hzI'
    obtain ⟨a, ha, haz⟩ := hzI'
    change (a : L₁ × L₂).fst = 0 at ha
    change (a : L₁ × L₂).snd = z at haz
    let := Fintype.ofFinite ι₁
    let := Fintype.ofFinite ι₂
    have := (basisProd eι b₁ b₂ hA).isCartanSubalgebra
    have haC : a ∈ prodCartan eι b₁ b₂ := by
      rw [← mem_toLieSubmodule, ← rootSpace_zero_eq, LieModule.mem_genWeightSpace]
      rintro ⟨t, ht⟩
      refine ⟨1, ?_⟩
      have hfst : ⁅(t : L₁ × L₂).fst, (a : L₁ × L₂).fst⁆ = 0 := by
        rw [ha, lie_zero]
      have hsnd : ⁅(t : L₁ × L₂).snd, (a : L₁ × L₂).snd⁆ = 0 := by
        rw [haz]
        exact lie_snd_eq_zero_of_mem_prodCartan eι b₁ b₂ ht ⟨z, hzH⟩
      simpa [Subtype.ext_iff] using And.intro hfst hsnd
    have ha0 : (⟨a, haC⟩ : prodCartan eι b₁ b₂) = 0 := by
      apply (prodCartanEquiv eι b₁ b₂).injective
      apply Subtype.ext
      exact ha
    have hz0 : z = 0 := by
      have heq : a = 0 := congrArg Subtype.val ha0
      have heq₂ := congrArg p₂ heq
      change (a : L₁ × L₂).snd = 0 at heq₂
      exact haz.symm.trans heq₂
    simpa only [LieSubmodule.mem_bot] using hz0
  have hzero : I = ⊥ := ReductiveGroups.lieIdeal_eq_bot_of_cartan_inf I hinf
  have hle : p₁.ker ≤ p₂.ker := by
    rw [← LieIdeal.map_eq_bot_iff]
    exact hzero
  have hdisj : Disjoint p₁.ker p₂.ker := by
    rw [disjoint_iff, _root_.eq_bot_iff]
    rintro ⟨⟨a, b⟩, -⟩
    simp [p₁, p₂, Subtype.ext_iff]
  change Injective p₁
  rw [← p₁.ker_eq_bot, hdisj.eq_bot_of_le hle]

/-- The paired-generator algebra projects isomorphically to its first factor. -/
private def killingProdEquivLeft : (prod eι b₁ b₂) ≃ₗ⁅K⁆ L₁ :=
  LieEquiv.ofBijective ((LieHom.fst K L₁ L₂).comp ((prod eι b₁ b₂)).incl)
    ⟨basisProd_fst_injective eι b₁ b₂ hA, surjective_fst_prod eι b₁ b₂⟩

variable [LieAlgebra.IsKilling K L₁] [H₁.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H₁ L₁]

/-- Split Killing Lie algebras with matching bases are isomorphic. -/
def equivOfKilling : L₁ ≃ₗ⁅K⁆ L₂ :=
  (killingProdEquivLeft eι b₁ b₂ hA).symm.trans
    ((prodSymmEquiv eι b₁ b₂).symm.trans
      (killingProdEquivLeft eι.symm b₂ b₁ (by simp [← hA])))

/-- The comparison identifies corresponding Cartan generators. -/
theorem equivOfKilling_h (i : ι₁) :
    equivOfKilling eι b₁ b₂ hA (b₁.h i) = b₂.h (eι i) := by
  have ha : (killingProdEquivLeft eι b₁ b₂ hA).symm (b₁.h i) = prodH eι b₁ b₂ i := by
    apply (killingProdEquivLeft eι b₁ b₂ hA).injective
    change (killingProdEquivLeft eι b₁ b₂ hA)
      ((killingProdEquivLeft eι b₁ b₂ hA).symm (b₁.h i)) = b₁.h i
    exact (killingProdEquivLeft eι b₁ b₂ hA).apply_symm_apply _
  unfold equivOfKilling
  simp only [LieEquiv.trans_apply, ha]
  rfl

/-- The comparison identifies corresponding positive generators. -/
theorem equivOfKilling_e (i : ι₁) :
    equivOfKilling eι b₁ b₂ hA (b₁.e i) = b₂.e (eι i) := by
  have ha : (killingProdEquivLeft eι b₁ b₂ hA).symm (b₁.e i) = prodE eι b₁ b₂ i := by
    apply (killingProdEquivLeft eι b₁ b₂ hA).injective
    change (killingProdEquivLeft eι b₁ b₂ hA)
      ((killingProdEquivLeft eι b₁ b₂ hA).symm (b₁.e i)) = b₁.e i
    exact (killingProdEquivLeft eι b₁ b₂ hA).apply_symm_apply _
  unfold equivOfKilling
  simp only [LieEquiv.trans_apply, ha]
  rfl

/-- The comparison identifies corresponding negative generators. -/
theorem equivOfKilling_f (i : ι₁) :
    equivOfKilling eι b₁ b₂ hA (b₁.f i) = b₂.f (eι i) := by
  have ha : (killingProdEquivLeft eι b₁ b₂ hA).symm (b₁.f i) = prodF eι b₁ b₂ i := by
    apply (killingProdEquivLeft eι b₁ b₂ hA).injective
    change (killingProdEquivLeft eι b₁ b₂ hA)
      ((killingProdEquivLeft eι b₁ b₂ hA).symm (b₁.f i)) = b₁.f i
    exact (killingProdEquivLeft eι b₁ b₂ hA).apply_symm_apply _
  unfold equivOfKilling
  simp only [LieEquiv.trans_apply, ha]
  rfl

end Field

end ReductiveGroups.LieBasis
