module

public import ThomGame.Quantum.ProjectiveMeasurement

/-! Finite-dimensional Hilbert-space geometry used by the POVM dilation. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Two isometric copies of the same space inside a finite-dimensional space
are related by a unitary on the ambient space. -/
theorem exists_unitary_extension [FiniteDimensional ℂ K]
    (V W : H →ₗᵢ[ℂ] K) :
    ∃ U : K ≃ₗᵢ[ℂ] K, ∀ ξ, U (V ξ) = W ξ := by
  let L := W.comp V.equivRange.symm.toLinearIsometry
  let U := L.extend
  let e := LinearIsometryEquiv.ofSurjective U
    (LinearMap.surjective_of_injective U.injective)
  refine ⟨e, fun ξ => ?_⟩
  change L.extend (V ξ) = W ξ
  calc
    L.extend (V ξ) = L (V.equivRange ξ) := L.extend_apply (V.equivRange ξ)
    _ = W ξ := by
      change W (V.equivRange.symm (V.equivRange ξ)) = W ξ
      rw [V.equivRange.symm_apply_apply]

namespace ProjectiveMeasurement

variable [CompleteSpace H] [CompleteSpace K] {O : Type*} [Fintype O]

/-- Transport a projective measurement along a unitary equivalence. -/
noncomputable def pullback (P : ProjectiveMeasurement K O) (e : H ≃ₗᵢ[ℂ] K) :
    ProjectiveMeasurement H O where
  proj a := e.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L P.proj a ∘L
    e.toContinuousLinearEquiv.toContinuousLinearMap
  selfAdjoint a := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro ξ ζ
    change inner ℂ (e.symm (P.proj a (e ξ))) ζ =
      inner ℂ ξ (e.symm (P.proj a (e ζ)))
    rw [← e.inner_map_map (e.symm (P.proj a (e ξ))) ζ,
      ← e.inner_map_map ξ (e.symm (P.proj a (e ζ)))]
    simpa using (P.selfAdjoint a).isSymmetric (e ξ) (e ζ)
  idempotent a := by
    ext ξ
    change e.symm (P.proj a (e (e.symm (P.proj a (e ξ))))) =
      e.symm (P.proj a (e ξ))
    simp [P.apply_twice]
  orthogonal a b hab := by
    ext ξ
    change e.symm (P.proj a (e (e.symm (P.proj b (e ξ))))) = 0
    rw [e.apply_symm_apply, ← mul_apply_eq_comp, P.orthogonal a b hab]
    simp
  complete := by
    ext ξ
    change (∑ a, (e.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L P.proj a ∘L
      e.toContinuousLinearEquiv.toContinuousLinearMap)) ξ = ξ
    simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
    rw [← map_sum, P.sum_apply, e.symm_apply_apply]

@[simp] theorem pullback_apply (P : ProjectiveMeasurement K O) (e : H ≃ₗᵢ[ℂ] K)
    (a : O) (ξ : H) : (P.pullback e).proj a ξ = e.symm (P.proj a (e ξ)) := rfl

theorem pullback_inner (P : ProjectiveMeasurement K O) (e : H ≃ₗᵢ[ℂ] K)
    (a : O) (ξ ζ : H) :
    inner ℂ ξ ((P.pullback e).proj a ζ) = inner ℂ (e ξ) (P.proj a (e ζ)) := by
  rw [pullback_apply, ← e.inner_map_map ξ (e.symm (P.proj a (e ζ))), e.apply_symm_apply]

end ProjectiveMeasurement

namespace Naimark

variable {O : Type*} [Fintype O] [DecidableEq O] [CompleteSpace H]

/-- The orthogonal direct sum of one copy of `H` per outcome. -/
abbrev DilationSpace (H O : Type*) := PiLp 2 (fun _ : O => H)

/-- Include the original Hilbert space in a fixed outcome summand. -/
noncomputable def inclusion (a : O) : H →ₗᵢ[ℂ] DilationSpace H O := by
  classical
  exact {
    toFun := fun ξ => (PiLp.single 2 a ξ : DilationSpace H O)
    map_add' := fun ξ ζ => PiLp.single_add 2 a
    map_smul' := fun c ξ => by
      ext b
      by_cases h : b = a <;> simp [h]
    norm_map' := fun ξ => by simp }

omit [CompleteSpace H] in
@[simp] theorem inclusion_apply (a : O) (ξ : H) :
    inclusion a ξ = PiLp.single 2 a ξ := rfl

/-- The coordinate projections form a projective measurement on the dilation space. -/
noncomputable def coordinates : ProjectiveMeasurement (DilationSpace H O) O := by
  classical
  exact {
    proj := fun a => (inclusion a).toContinuousLinearMap ∘L PiLp.proj 2 _ a
    selfAdjoint := fun a => by
      apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      intro ξ ζ
      change inner ℂ (PiLp.single 2 a (ξ a)) ζ =
        inner ℂ ξ (PiLp.single 2 a (ζ a))
      simp only [PiLp.inner_apply, PiLp.single_apply]
      rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
      · simp
      · intro b _ hba
        simp [hba]
      · simp
      · intro b _ hba
        simp [hba]
      · simp
    idempotent := fun a => by
      ext ξ b
      change (PiLp.single 2 (β := fun _ : O => H) a
        ((PiLp.single 2 (β := fun _ : O => H) a (ξ a)) a)) b =
        (PiLp.single 2 (β := fun _ : O => H) a (ξ a)) b
      simp
    orthogonal := fun a b hab => by
      ext ξ c
      change (PiLp.single 2 (β := fun _ : O => H) a
        ((PiLp.single 2 (β := fun _ : O => H) b (ξ b)) a)) c = 0
      simp [PiLp.single_apply, hab]
    complete := by
      ext ξ a
      change ((∑ b, ((inclusion (H := H) b).toContinuousLinearMap ∘L
        PiLp.proj 2 (fun _ : O => H) b)) ξ) a = ξ a
      simp [_root_.sum_apply] }

@[simp] theorem coordinates_apply (a : O) (ξ : DilationSpace H O) :
    (coordinates (H := H) (O := O)).proj a ξ = PiLp.single 2 a (ξ a) := rfl

theorem coordinates_inner (a : O) (ξ ζ : DilationSpace H O) :
    inner ℂ ξ ((coordinates (H := H) (O := O)).proj a ζ) = inner ℂ (ξ a) (ζ a) := by
  classical
  simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]

end Naimark
end ThomGame.Quantum
