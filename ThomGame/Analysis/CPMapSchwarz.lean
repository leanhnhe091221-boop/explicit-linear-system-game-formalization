module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Schwarz inequality for actual unital completely positive maps

Positivity of the two-by-two Gram matrix gives adjoint preservation.
Conjugating its image by the column (-F(x),1) proves the operator-valued
Schwarz inequality, with no representation or Kraus decomposition assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped CStarAlgebra BigOperators

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem cstarMatrix_diagonal_nonneg {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι A) (hM : 0 ≤ M) (i : ι) : 0 ≤ M i i := by
  rw [StarOrderedRing.nonneg_iff] at hM
  refine AddSubmonoid.closure_induction (fun X hX => ?_) (by exact le_rfl)
    (fun X Y _ _ hX hY => add_nonneg hX hY) hM
  obtain ⟨V, rfl⟩ := hX
  change 0 ≤ ∑ j, star (V j i) * V j i
  exact Finset.sum_nonneg (fun j _ => star_mul_self_nonneg (V j i))

theorem cstarMatrix_two_gram_nonneg (x : A) :
    0 ≤ CStarMatrix.ofMatrix !![(1 : A), x; star x, star x * x] := by
  let V : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![(1 : A), x; 0, 0]
  have he : star V * V = CStarMatrix.ofMatrix !![(1 : A), x; star x, star x * x] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose, Fin.sum_univ_two]
  rw [← he]
  exact star_mul_self_nonneg V

theorem completelyPositiveMap_star (F : A →CP B) (x : A) : F (star x) = star (F x) := by
  have hp := F.map_cstarMatrix_nonneg _ (cstarMatrix_two_gram_nonneg x)
  have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) B => M 1 0) hp.isSelfAdjoint.star_eq
  simpa [CStarMatrix.star_eq_conjTranspose] using he.symm

theorem completelyPositiveMap_schwarz (F : A →CP B) (hF : F 1 = 1) (x : A) :
    star (F x) * F x ≤ F (star x * x) := by
  let G : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![(1 : A), x; star x, star x * x]
  let V : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix !![-F x, 0; (1 : B), 0]
  have hp : 0 ≤ star V * (G.map F) * V :=
    star_left_conjugate_nonneg (F.map_cstarMatrix_nonneg G (cstarMatrix_two_gram_nonneg x)) V
  have he : (star V * (G.map F) * V) 0 0 = F (star x * x) - star (F x) * F x := by
    simp [V, G, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      Fin.sum_univ_two, hF, completelyPositiveMap_star]
    abel
  have hn := cstarMatrix_diagonal_nonneg _ hp (0 : Fin 2)
  rw [he] at hn
  exact sub_nonneg.mp hn

theorem completelyPositiveMap_norm_le (F : A →CP B) (hF : F 1 = 1) (x : A) :
    ‖F x‖ ≤ ‖x‖ := by
  have hc : F (algebraMap ℝ A (‖x‖ ^ 2)) = algebraMap ℝ B (‖x‖ ^ 2) := by
    simp only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, hF]
  have ho := OrderHomClass.mono F (CStarAlgebra.star_mul_le_algebraMap_norm_sq x)
  rw [hc] at ho
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap (star (F x) * F x)
    (sq_nonneg ‖x‖) (star_mul_self_nonneg (F x))).mpr ((completelyPositiveMap_schwarz F hF x).trans ho)
  rw [CStarRing.norm_star_mul_self, ← sq] at hn
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

end ThomGame.Analysis
