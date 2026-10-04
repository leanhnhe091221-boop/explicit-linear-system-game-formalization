module

public import ThomGame.Quantum.FinitePOVMStrategy
public import ThomGame.Quantum.TensorCompression

/-! The concrete finite-dimensional POVM model covers arbitrary finite Hilbert spaces.

Choosing orthonormal coordinates transports both local measurements and the single
bipartite unit state, preserving every Born probability. Positive local dimensions
follow from the existence of that unit state.
-/

@[expose] public section
namespace ThomGame.Quantum

open scoped TensorProduct BigOperators

namespace POVM

variable {H K O : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [Fintype O]

/-- Transport a POVM by a unitary change of Hilbert-space coordinates. -/
noncomputable def congr (P : POVM H O) (U : H ≃ₗᵢ[ℂ] K) : POVM K O where
  effect a := U.conjStarAlgEquiv (P.effect a)
  positive a := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, ← U.adjoint_eq_symm]
    exact (P.isPositive a).conj_adjoint (U : H →L[ℂ] K)
  complete := by rw [← map_sum, P.complete, map_one]

theorem congr_inner (P : POVM H O) (U : H ≃ₗᵢ[ℂ] K) (a : O) (ξ ζ : H) :
    inner ℂ (U ξ) ((P.congr U).effect a (U ζ)) = inner ℂ ξ (P.effect a ζ) := by
  simp only [congr, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, U.inner_map_map]

end POVM

namespace FinitePOVMStrategy

variable {X Y A B H K : Type*} [Fintype A] [Fintype B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-- Every POVM strategy on arbitrary finite-dimensional local Hilbert spaces has
exactly the same full correlation table as a strategy in the concrete coordinate model.
The chosen state and coordinate maps are independent of the questions. -/
theorem exists_coordinates (ψ : H ⊗[ℂ] K) (hψ : ‖ψ‖ = 1)
    (M : X → POVM H A) (N : Y → POVM K B) :
    ∃ S : FinitePOVMStrategy X Y A B, S.correlation =
      fun x y a b => (inner ℂ ψ (TensorProduct.mapL ((M x).effect a) ((N y).effect b) ψ)).re := by
  letI : CompleteSpace H := FiniteDimensional.complete ℂ H
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  letI : CompleteSpace (H ⊗[ℂ] K) := FiniteDimensional.complete ℂ _
  have hψne : ψ ≠ 0 := by
    intro hz
    simpa [hz] using hψ
  haveI : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with h | h
    · letI := h
      exact False.elim (hψne (Subsingleton.elim _ _))
    · exact h
  haveI : Nontrivial K := by
    rcases subsingleton_or_nontrivial K with h | h
    · letI := h
      exact False.elim (hψne (Subsingleton.elim _ _))
    · exact h
  let U := (stdOrthonormalBasis ℂ H).repr
  let V := (stdOrthonormalBasis ℂ K).repr
  let S : FinitePOVMStrategy X Y A B := {
    dimAlice := Module.finrank ℂ H
    dimBob := Module.finrank ℂ K
    dimAlice_pos := Module.finrank_pos
    dimBob_pos := Module.finrank_pos
    state := TensorProduct.mapIsometry U.toLinearIsometry V.toLinearIsometry ψ
    norm_state := (TensorProduct.mapIsometry U.toLinearIsometry V.toLinearIsometry).norm_map ψ
      |>.trans hψ
    alice x := (M x).congr U
    bob y := (N y).congr V }
  refine ⟨S, ?_⟩
  funext x y a b
  exact re_inner_tensor_compression_of_inner U.toLinearIsometry V.toLinearIsometry
    ((M x).congr U |>.effect a) ((N y).congr V |>.effect b)
    ((M x).effect a) ((N y).effect b)
    ((M x).congr_inner U a) ((N y).congr_inner V b) ψ

end FinitePOVMStrategy

end ThomGame.Quantum
