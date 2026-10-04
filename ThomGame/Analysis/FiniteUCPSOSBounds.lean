module

public import ThomGame.Analysis.FiniteUCPWeakGapHeat
public import ThomGame.Analysis.MatrixMarkovPerturbation
public import ThomGame.Analysis.RelatorAreaCalculus
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.List.OfFn

/-! Finite real quadratic-form estimates for transferring an exact rational
sum-of-squares certificate through short-word relator equalities. -/

@[expose] public section
namespace ThomGame.Analysis
open scoped BigOperators

theorem finiteSOS_zero_sum_weighted_bound {ι : Type*} [Fintype ι]
    (c e : ι → ℝ) {B : ℝ} (hsum : ∑ i, c i = 0)
    (he0 : ∀ i, 0 ≤ e i) (heB : ∀ i, e i ≤ B) :
    ∑ i, c i * e i ≤ (B / 2) * ∑ i, |c i| := by
  have hp (i : ι) : c i * e i ≤ (B / 2) * (|c i| + c i) := by
    by_cases hi : 0 ≤ c i
    · rw [abs_of_nonneg hi]
      have hh := mul_le_mul_of_nonneg_left (heB i) hi
      nlinarith
    · have hi' : c i ≤ 0 := le_of_not_ge hi
      rw [abs_of_nonpos hi']
      have hh := mul_nonpos_of_nonpos_of_nonneg hi' (he0 i)
      nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hsum, add_zero] using hh

section RealHilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem finiteSOS_residual_bound {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (x : H) (y : ι → H) {D mass : ℝ}
    (hD : 0 ≤ D) (hsum : ∑ i, c i = 0) (hmass : ∑ i, |c i| ≤ mass)
    (hnorm : ∀ i, ‖y i‖ = ‖x‖) (hword : ∀ i, ‖x - y i‖ ^ 2 ≤ 16 * D) :
    -(4 * mass * D) ≤ ∑ i, c i * inner ℝ x (y i) := by
  have hid (i : ι) : ‖x‖ ^ 2 - inner ℝ x (y i) = ‖x - y i‖ ^ 2 / 2 := by
    have hh := norm_sub_sq_real x (y i)
    rw [hnorm i] at hh
    linarith
  have he0 (i : ι) : 0 ≤ ‖x‖ ^ 2 - inner ℝ x (y i) := by rw [hid]; positivity
  have heB (i : ι) : ‖x‖ ^ 2 - inner ℝ x (y i) ≤ 8 * D := by
    rw [hid]
    linarith [hword i]
  have hh := finiteSOS_zero_sum_weighted_bound c
    (fun i => ‖x‖ ^ 2 - inner ℝ x (y i)) hsum he0 heB
  have he : ∑ i, c i * (‖x‖ ^ 2 - inner ℝ x (y i)) =
      -(∑ i, c i * inner ℝ x (y i)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_sub]
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ (8 * D) / 2 by positivity)
  nlinarith

theorem finiteSOS_gram_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → ℝ) (y : ι → H) :
    ∑ i, ∑ j, (∑ k, c i k * c j k) * inner ℝ (y i) (y j) =
      ∑ k, ‖∑ i, c i k • y i‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  simp_rw [mul_assoc]
  calc
    (∑ i, ∑ j, ∑ k, c i k * (c j k * inner ℝ (y i) (y j))) =
        ∑ i, ∑ k, ∑ j, c i k * (c j k * inner ℝ (y i) (y j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem finiteSOS_gram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → ℝ) (y : ι → H) :
    0 ≤ ∑ i, ∑ j, (∑ k, c i k * c j k) * inner ℝ (y i) (y j) := by
  rw [finiteSOS_gram_identity]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end RealHilbert

theorem finiteSOS_coefficient_transfer {ι : Type*} [Fintype ι]
    (c a b : ι → ℝ) {err : ℝ} (h : ∀ i, |a i - b i| ≤ err) :
    |(∑ i, c i * a i) - ∑ i, c i * b i| ≤ (∑ i, |c i|) * err := by
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ i, |c i * (a i - b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * err := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- Quantitative numerical end of the NT argument, retaining the displayed
SOS and residual terms and the independently bounded lifting error. -/
theorem finiteSOS_NT_numerical_repair {energy square sos residual defect : ℝ}
    (henergy : 0 ≤ energy) (hsos : 0 ≤ sos)
    (hresidual : -(9 / 100 : ℝ) * energy ≤ residual)
    (hlift : |square - (561 / 2000 : ℝ) * energy - sos - residual| ≤
      10000000 * defect) :
    (1 / 6 : ℝ) * energy ≤ square + 10000000 * defect := by
  have hh := (abs_le.mp hlift).1
  linarith

theorem finiteSOS_NT_normalization {energy defectSquare δ : ℝ} (hδ : 0 ≤ δ)
    (h : (1 / 6 : ℝ) * (24 * energy) ≤ 576 * defectSquare + 10000000 * δ) :
    (1 / 144 : ℝ) * energy ≤ defectSquare + 1000000000 * δ := by
  linarith

theorem finiteSOS_sum_get {ι : Type*} (l : List ι) (f : ι → ℝ) :
    (∑ i : Fin l.length, f l[i.val]) = (l.map f).sum := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]

theorem finiteSOS_coefficient_transfer_list {ι : Type*} (l : List ι)
    (c a b : ι → ℝ) {err : ℝ} (h : ∀ i ∈ l, |a i - b i| ≤ err) :
    |(l.map (fun i => c i * a i)).sum - (l.map (fun i => c i * b i)).sum| ≤
      (l.map (fun i => |c i|)).sum * err := by
  have hh := finiteSOS_coefficient_transfer (fun i : Fin l.length => c l[i.val])
    (fun i : Fin l.length => a l[i.val]) (fun i : Fin l.length => b l[i.val])
    (fun i => h l[i.val] (List.getElem_mem i.isLt))
  rw [finiteSOS_sum_get l (fun i => c i * a i),
    finiteSOS_sum_get l (fun i => c i * b i), finiteSOS_sum_get l (fun i => |c i|)] at hh
  exact hh

theorem finiteSOS_residual_bound_list {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (l : List ι)
    (c : ι → ℝ) (x : H) (y : ι → H) {D mass : ℝ}
    (hD : 0 ≤ D) (hsum : (l.map c).sum = 0)
    (hmass : (l.map (fun i => |c i|)).sum ≤ mass)
    (hnorm : ∀ i ∈ l, ‖y i‖ = ‖x‖)
    (hword : ∀ i ∈ l, ‖x - y i‖ ^ 2 ≤ 16 * D) :
    -(4 * mass * D) ≤ (l.map (fun i => c i * inner ℝ x (y i))).sum := by
  have hh := finiteSOS_residual_bound (mass := mass) (fun i : Fin l.length => c l[i.val]) x
    (fun i : Fin l.length => y l[i.val]) hD
    (by rw [finiteSOS_sum_get l c]; exact hsum)
    (by rw [finiteSOS_sum_get l (fun i => |c i|)]; exact hmass)
    (fun i => hnorm l[i.val] (List.getElem_mem i.isLt))
    (fun i => hword l[i.val] (List.getElem_mem i.isLt))
  rw [finiteSOS_sum_get l (fun i => c i * inner ℝ x (y i))] at hh
  exact hh

end ThomGame.Analysis
