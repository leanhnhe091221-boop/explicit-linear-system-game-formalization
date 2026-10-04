module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section
namespace ThomGame.Analysis
open scoped BigOperators

theorem finiteThreePairCombination {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x : H) (v : Fin 3 → H) {η : ℝ}
    (hp : ∀ i : Fin 3, (11 / 20 : ℝ) * (inner ℂ x (v i + v (i+1))).re ≤
      ‖v i + v (i+1)‖ ^ 2 + 18 * η)
    (hi : ∀ i : Fin 3, ‖v i‖ ^ 2 ≤ (inner ℂ x (v i)).re + 5 * η) :
    (1 / 10 : ℝ) * (inner ℂ x (∑ i : Fin 3, v i)).re ≤
      ‖∑ i : Fin 3, v i‖ ^ 2 + 69 * η := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  norm_num only [show (0+1 : Fin 3) = 1 from rfl,
    show (1+1 : Fin 3) = 2 from rfl, show (2+1 : Fin 3) = 0 from rfl] at hp0 hp1 hp2
  have h01 := norm_add_sq (𝕜 := ℂ) (v 0) (v 1)
  have h12 := norm_add_sq (𝕜 := ℂ) (v 1) (v 2)
  have h20 := norm_add_sq (𝕜 := ℂ) (v 2) (v 0)
  have hall := norm_add_sq (𝕜 := ℂ) (v 0) (v 1 + v 2)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at ⊢
  simp only [inner_add_right, RCLike.re_to_complex, Complex.add_re] at hp0 hp1 hp2 hall ⊢
  have hs := inner_re_symm (𝕜 := ℂ) (v 0) (v 2)
  simp only [RCLike.re_to_complex] at h01 h12 h20 hs
  nlinarith

end ThomGame.Analysis
