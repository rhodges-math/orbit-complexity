import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed

/-!
# Connected Group Translation

Points from a connected affine group fix all idempotent functions under
translation. This applies to torus generators as well as additive generators. -/

noncomputable section
namespace ReductiveGroups
open WithConv

universe u
variable {K B D : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
  [CommRing D] [Algebra K D] [ConnectedSpace (PrimeSpectrum D)]

/-- A path valued in a connected affine scheme, with one specialization at
the identity, fixes idempotents under every other specialization's translation. -/
theorem RightTranslation.fixes_idempotent_of_connected_path
    (e : B) (he : IsIdempotentElem e)
    (g : WithConv (B →ₐ[K] K)) (x : WithConv (B →ₐ[K] D))
    (φ ψ : D →ₐ[K] K)
    (hφ : TauCeti.AlgHom.mapValue (H := B) φ x = g)
    (hψ : TauCeti.AlgHom.mapValue (H := B) ψ x = 1) :
    TauCeti.HopfAlgebra.rightTranslationAlgHom g e = e := by
  apply TauCeti.eq_of_isIdempotentElem_of_forall_algHom_apply_eq
    (k := K) (A := B) (K := K) (he.map _) he
  intro f
  let c : WithConv (B →ₐ[K] D) :=
    TauCeti.AlgHom.mapValue (H := B) (IsScalarTower.toAlgHom K K D) (toConv f)
  have hc (θ : D →ₐ[K] K) :
      TauCeti.AlgHom.mapValue (H := B) θ c = toConv f := by
    have hcomp : θ.comp (IsScalarTower.toAlgHom K K D) = AlgHom.id K K :=
      AlgHom.ext fun z => θ.commutes z
    dsimp only [c]
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapValue_comp, hcomp,
      TauCeti.AlgHom.mapValue_id, MonoidHom.id_apply]
  have heq : φ ((c * x).ofConv e) = ψ ((c * x).ofConv e) := by
    rcases TauCeti.eq_zero_or_eq_one_of_isIdempotentElem
      (he.map (c * x).ofConv) with h | h <;> simp [h]
  have hpath :
      (TauCeti.AlgHom.mapValue (H := B) φ (c * x)).ofConv e =
        (TauCeti.AlgHom.mapValue (H := B) ψ (c * x)).ofConv e := heq
  rw [map_mul, hc φ, hφ] at hpath
  rw [map_mul, hc ψ, hψ, mul_one] at hpath
  exact (TauCeti.HopfAlgebra.ofConv_rightTranslationAlgHom (toConv f) g e).trans hpath

/-- The image of any point of a connected affine group fixes all ambient
idempotents. Neither smoothness nor injectivity of the group morphism is needed. -/
theorem ConnectedGroupPoint.rightTranslation_fixes_idempotent
    {E : Type u} [CommRing E] [HopfAlgebra K E]
    [ConnectedSpace (PrimeSpectrum E)] (q : B →ₐc[K] E)
    (p : WithConv (E →ₐ[K] K)) (e : B) (he : IsIdempotentElem e) :
    TauCeti.HopfAlgebra.rightTranslationAlgHom
      (TauCeti.AlgHom.mapDomain q p) e = e := by
  apply RightTranslation.fixes_idempotent_of_connected_path e he
    (TauCeti.AlgHom.mapDomain q p) (toConv q.toAlgHom)
    p.ofConv (Bialgebra.counitAlgHom K E)
  · rfl
  · change toConv ((Bialgebra.counitAlgHom K E).comp q.toAlgHom) = 1
    apply WithConv.ofConv_injective
    ext b
    exact CoalgHomClass.counit_comp_apply q b

end ReductiveGroups
