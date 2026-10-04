module

public import ThomGame.Analysis.MatrixTraceRightAction
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! Actual unitary conjugation on the complete Hilbert space of the normalized matrix trace. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (L : Ultrafilter ι)

def matrixHilbertConjugationOperator (u : unitary (MatrixTracialQuotient dims (L : Filter ι))) :
    MatrixTraceHilbert dims hd L →L[ℂ] MatrixTraceHilbert dims hd L :=
  matrixLeftOperator dims hd L u.val * matrixRightOperator dims hd L (star u.val)

theorem matrixHilbertConjugationOperator_embedding
    (u : unitary (MatrixTracialQuotient dims (L : Filter ι)))
    (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixHilbertConjugationOperator dims hd L u (matrixHilbertEmbedding dims hd L x) =
      matrixHilbertEmbedding dims hd L (Unitary.conjStarAlgAut ℂ _ u x) := by
  simp only [matrixHilbertConjugationOperator, mul_apply_eq_comp, matrixRightOperator_apply,
    matrixLeftOperator_apply, Unitary.conjStarAlgAut_apply, mul_assoc]

theorem matrixUltratrace_conjugation (u : unitary (MatrixTracialQuotient dims (L : Filter ι)))
    (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixUltratrace dims hd L (Unitary.conjStarAlgAut ℂ _ u x) = matrixUltratrace dims hd L x := by
  rw [Unitary.conjStarAlgAut_apply, matrixUltratrace_mul_comm,
    ← mul_assoc, u.property.1, one_mul]

theorem matrixHilbertConjugationOperator_one :
    matrixHilbertConjugationOperator dims hd L 1 = 1 := by
  apply matrixHilbertOperator_ext dims hd L
  intro x
  rw [matrixHilbertConjugationOperator_embedding, map_one]
  rfl

theorem matrixHilbertConjugationOperator_mul
    (u v : unitary (MatrixTracialQuotient dims (L : Filter ι))) :
    matrixHilbertConjugationOperator dims hd L (u * v) =
      matrixHilbertConjugationOperator dims hd L u * matrixHilbertConjugationOperator dims hd L v := by
  apply matrixHilbertOperator_ext dims hd L
  intro x
  simp only [mul_apply_eq_comp, matrixHilbertConjugationOperator_embedding,
    Unitary.conjStarAlgAut_mul_apply]

theorem matrixHilbertConjugationOperator_norm
    (u : unitary (MatrixTracialQuotient dims (L : Filter ι))) (ξ : MatrixTraceHilbert dims hd L) :
    ‖matrixHilbertConjugationOperator dims hd L u ξ‖ = ‖ξ‖ := by
  refine (matrixHilbertEmbedding_dense dims hd L).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  rw [matrixHilbertConjugationOperator_embedding]
  have hin : inner ℂ (matrixHilbertEmbedding dims hd L (Unitary.conjStarAlgAut ℂ _ u x))
      (matrixHilbertEmbedding dims hd L (Unitary.conjStarAlgAut ℂ _ u x)) =
      inner ℂ (matrixHilbertEmbedding dims hd L x) (matrixHilbertEmbedding dims hd L x) := by
    rw [matrixHilbertEmbedding_inner, matrixHilbertEmbedding_inner, ← map_star, ← map_mul,
      matrixUltratrace_conjugation]
  have hn := congrArg (fun z : ℂ => z.re) hin
  have ha := norm_sq_eq_re_inner (𝕜 := ℂ)
    (matrixHilbertEmbedding dims hd L (Unitary.conjStarAlgAut ℂ _ u x))
  have hb := norm_sq_eq_re_inner (𝕜 := ℂ) (matrixHilbertEmbedding dims hd L x)
  simp only [RCLike.re_to_complex] at ha hb
  nlinarith [norm_nonneg (matrixHilbertEmbedding dims hd L (Unitary.conjStarAlgAut ℂ _ u x)),
    norm_nonneg (matrixHilbertEmbedding dims hd L x)]

def matrixHilbertConjugation (u : unitary (MatrixTracialQuotient dims (L : Filter ι))) :
    MatrixTraceHilbert dims hd L ≃ₗᵢ[ℂ] MatrixTraceHilbert dims hd L where
  toLinearMap := (matrixHilbertConjugationOperator dims hd L u).toLinearMap
  invFun := matrixHilbertConjugationOperator dims hd L u⁻¹
  left_inv ξ := by
    change (matrixHilbertConjugationOperator dims hd L u⁻¹ * matrixHilbertConjugationOperator dims hd L u) ξ = ξ
    rw [← matrixHilbertConjugationOperator_mul, inv_mul_cancel, matrixHilbertConjugationOperator_one]
    rfl
  right_inv ξ := by
    change (matrixHilbertConjugationOperator dims hd L u * matrixHilbertConjugationOperator dims hd L u⁻¹) ξ = ξ
    rw [← matrixHilbertConjugationOperator_mul, mul_inv_cancel, matrixHilbertConjugationOperator_one]
    rfl
  norm_map' := matrixHilbertConjugationOperator_norm dims hd L u

theorem matrixHilbertConjugation_embedding
    (u : unitary (MatrixTracialQuotient dims (L : Filter ι))) (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixHilbertConjugation dims hd L u (matrixHilbertEmbedding dims hd L x) =
      matrixHilbertEmbedding dims hd L (u.val * x * star u.val) :=
  matrixHilbertConjugationOperator_embedding dims hd L u x

def matrixHilbertConjugationHom : unitary (MatrixTracialQuotient dims (L : Filter ι)) →*
    (MatrixTraceHilbert dims hd L ≃ₗᵢ[ℂ] MatrixTraceHilbert dims hd L) where
  toFun := matrixHilbertConjugation dims hd L
  map_one' := by
    ext ξ
    exact DFunLike.congr_fun (matrixHilbertConjugationOperator_one dims hd L) ξ
  map_mul' u v := by
    ext ξ
    exact DFunLike.congr_fun (matrixHilbertConjugationOperator_mul dims hd L u v) ξ

theorem matrixHilbertConjugationHom_embedding
    (u : unitary (MatrixTracialQuotient dims (L : Filter ι))) (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixHilbertConjugationHom dims hd L u (matrixHilbertEmbedding dims hd L x) =
      matrixHilbertEmbedding dims hd L (u.val * x * star u.val) :=
  matrixHilbertConjugation_embedding dims hd L u x

theorem matrixHilbertConjugationHom_symm_embedding
    (u : unitary (MatrixTracialQuotient dims (L : Filter ι))) (x : MatrixTracialQuotient dims (L : Filter ι)) :
    (matrixHilbertConjugationHom dims hd L u).symm (matrixHilbertEmbedding dims hd L x) =
      matrixHilbertEmbedding dims hd L (star u.val * x * u.val) := by
  change matrixHilbertConjugationOperator dims hd L u⁻¹ (matrixHilbertEmbedding dims hd L x) = _
  simpa only [Unitary.conjStarAlgAut_apply, ← Unitary.star_eq_inv, Unitary.coe_star, star_star] using
    matrixHilbertConjugationOperator_embedding dims hd L u⁻¹ x

end ThomGame.Analysis
