module

public import ThomGame.Certificates.NetzerThomPartition
public import ThomGame.Certificates.NetzerThomGramFormula
public import ThomGame.Certificates.NetzerThomWordCertificates
public import ThomGame.Certificates.NetzerThomClassMass

@[expose] public section
namespace ThomGame.Certificates.NetzerThom
noncomputable section
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def denominator : ℝ := 14641000000000000
def gramReal (ij : ℕ × ℕ) : ℝ := (gramEntry ij.1 ij.2 : ℝ) / denominator
def targetReal (i : ℕ) : ℝ := ((targetTerms.getD i ([],0)).2 : ℝ) / denominator
def residualReal (c : ResidualClass) : ℝ := (residualNumerator c : ℝ) / denominator

theorem denominator_pos : 0 < denominator := by norm_num [denominator]

theorem list_sum_div {α : Type*} (l : List α) (f : α → ℝ) (b : ℝ) :
    (l.map (fun x => f x / b)).sum = (l.map f).sum / b := by
  simp only [div_eq_mul_inv, List.sum_map_mul_right]

theorem list_int_sum_cast {α : Type*} (l : List α) (f : α → ℤ) :
    (l.map (fun x => (f x : ℝ))).sum = ((l.map f).sum : ℤ) := by
  rw [Int.cast_list_sum]
  simp only [List.map_map, Function.comp_def]

theorem list_int_abs_sum_cast {α : Type*} (l : List α) (f : α → ℤ) :
    (l.map (fun x => |(f x : ℝ)|)).sum = ((l.map (fun x => (f x).natAbs)).sum : ℕ) := by
  rw [Nat.cast_list_sum]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  have hh := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (f x))
  simpa only [Int.cast_natCast, Int.cast_abs] using hh.symm

theorem residualReal_sum : (residualClasses.map residualReal).sum = 0 := by
  unfold residualReal
  rw [list_sum_div, list_int_sum_cast, residual_augmentation]
  simp

theorem residualReal_mass : (residualClasses.map (fun c => |residualReal c|)).sum ≤ 9 / 400 := by
  simp only [residualReal, abs_div, abs_of_pos denominator_pos, list_sum_div,
    list_int_abs_sum_cast]
  change (residualMass : ℝ) / denominator ≤ _
  apply (div_le_iff₀ denominator_pos).mpr
  have h : (400 : ℝ) * residualMass ≤ 9 * denominator := by
    unfold denominator
    exact_mod_cast residualMass_bound
  linarith

theorem residualReal_formula (c : ResidualClass) : residualReal c =
    (c.terms.map targetReal).sum - (c.pairs.map gramReal).sum := by
  unfold residualReal targetReal gramReal
  simp only [residualNumerator,
    list_sum_div, list_int_sum_cast, Int.cast_sub, sub_div]

theorem gramReal_class_mass :
    (residualClasses.map (fun c => (c.pairs.map (fun ij => |gramReal ij|)).sum)).sum ≤ 20000 := by
  simp only [gramReal, abs_div, abs_of_pos denominator_pos, list_sum_div]
  simp only [list_int_abs_sum_cast]
  have he : (residualClasses.map (fun c =>
      (((c.pairs.map (fun ij => (gramEntry ij.1 ij.2).natAbs)).sum : ℕ) : ℝ))).sum =
      (((residualClasses.flatMap (fun c => c.pairs.map (fun ij => (gramEntry ij.1 ij.2).natAbs))).sum : ℕ) : ℝ) := by
    simp only [List.flatMap, List.sum_flatten, Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [he]
  apply (div_le_iff₀ denominator_pos).mpr
  unfold denominator
  exact_mod_cast gramClassMass_bound

theorem targetReal_class_mass :
    (residualClasses.map (fun c => (c.terms.map (fun i => |targetReal i|)).sum)).sum ≤ 600 := by
  simp only [targetReal, abs_div, abs_of_pos denominator_pos, list_sum_div]
  simp only [list_int_abs_sum_cast]
  have he : (residualClasses.map (fun c =>
      (((c.terms.map (fun i => (targetTerms.getD i ([],0)).2.natAbs)).sum : ℕ) : ℝ))).sum =
      (((residualClasses.flatMap (fun c => c.terms.map (fun i => (targetTerms.getD i ([],0)).2.natAbs))).sum : ℕ) : ℝ) := by
    simp only [List.flatMap, List.sum_flatten, Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [he]
  apply (div_le_iff₀ denominator_pos).mpr
  unfold denominator
  exact_mod_cast targetClassMass_bound

end
end ThomGame.Certificates.NetzerThom
