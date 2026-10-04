module

public import ThomGame.Quantum.POVM
public import ThomGame.Quantum.NaimarkGeometry

/-! Simultaneous finite-dimensional Naimark dilation.

Every family of finite POVMs admits projective measurements on one finite-dimensional
space, with one isometric embedding independent of the question. The construction
uses the square-root embedding for each POVM, then extends its isometry from a fixed
copy of the original space to a unitary on the common dilation space.
-/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

namespace POVM

variable {H O : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype O]

/-- The square-root column of a POVM is an isometry. -/
noncomputable def sqrtEmbedding (M : POVM H O) : H →ₗᵢ[ℂ] Naimark.DilationSpace H O where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (O → H)).symm.toLinearMap.comp
    (LinearMap.pi fun a => (M.root a).toLinearMap)
  norm_map' ξ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (fun a => M.root a ξ)‖ ^ 2 = ‖ξ‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2]
    exact M.sum_root_norm_sq ξ

@[simp] theorem sqrtEmbedding_apply (M : POVM H O) (ξ : H) (a : O) :
    M.sqrtEmbedding ξ a = M.root a ξ := rfl

theorem sqrtEmbedding_coordinates_inner [DecidableEq O] (M : POVM H O)
    (a : O) (ξ ζ : H) :
    inner ℂ (M.sqrtEmbedding ξ)
        ((Naimark.coordinates (H := H) (O := O)).proj a (M.sqrtEmbedding ζ)) =
      inner ℂ ξ (M.effect a ζ) := by
  rw [Naimark.coordinates_inner]
  change inner ℂ (M.root a ξ) (M.root a ζ) = inner ℂ ξ (M.effect a ζ)
  rw [← ContinuousLinearMap.adjoint_inner_right, (M.root_selfAdjoint a).adjoint_eq,
    ← mul_apply_eq_comp, M.root_mul_root]

/-- A family of finite-dimensional POVMs can be dilated simultaneously. The
embedding and enlarged local dimension are independent of the question. -/
theorem exists_projective_dilation [FiniteDimensional ℂ H] [Nontrivial H]
    [Nonempty O] {X : Type*} (M : X → POVM H O) :
    ∃ (n : Nat) (_ : 0 < n)
      (V : H →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
      (P : X → ProjectiveMeasurement (EuclideanSpace ℂ (Fin n)) O),
      ∀ x a ξ ζ, inner ℂ (V ξ) ((P x).proj a (V ζ)) =
        inner ℂ ξ ((M x).effect a ζ) := by
  classical
  let a₀ : O := Classical.choice inferInstance
  let V₀ : H →ₗᵢ[ℂ] Naimark.DilationSpace H O := Naimark.inclusion a₀
  have hU : ∀ x, ∃ U : Naimark.DilationSpace H O ≃ₗᵢ[ℂ] Naimark.DilationSpace H O,
      ∀ ξ, U (V₀ ξ) = (M x).sqrtEmbedding ξ :=
    fun x => exists_unitary_extension V₀ (M x).sqrtEmbedding
  choose U hU using hU
  let e := (stdOrthonormalBasis ℂ (Naimark.DilationSpace H O)).repr
  have : Nontrivial (Naimark.DilationSpace H O) :=
    Function.Injective.nontrivial V₀.injective
  refine ⟨Module.finrank ℂ (Naimark.DilationSpace H O),
    Module.finrank_pos, e.toLinearIsometry.comp V₀,
    fun x => ((Naimark.coordinates (H := H) (O := O)).pullback (U x)).pullback e.symm,
    fun x a ξ ζ => ?_⟩
  simp only [ProjectiveMeasurement.pullback_inner]
  change inner ℂ (U x (e.symm (e (V₀ ξ))))
    ((Naimark.coordinates (H := H) (O := O)).proj a (U x (e.symm (e (V₀ ζ))))) = _
  simp only [e.symm_apply_apply]
  rw [hU, hU]
  exact (M x).sqrtEmbedding_coordinates_inner a ξ ζ

end POVM
end ThomGame.Quantum
