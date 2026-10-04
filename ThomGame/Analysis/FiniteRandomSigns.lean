module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Finite independent signs and their second moment

Signs are the actual functions from a finite index type to `Bool`,
with the uniform finite average. Flipping one coordinate proves
vanishing mixed moments, hence the Hilbert-space second moment identity.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

def finiteSign (b : Bool) : ℝ := if b then 1 else -1

theorem finiteSign_not (b : Bool) : finiteSign (!b) = -finiteSign b := by
  cases b <;> norm_num [finiteSign]

theorem finiteSign_sq (b : Bool) : finiteSign b ^ 2 = 1 := by
  cases b <;> norm_num [finiteSign]

variable {ι : Type*}

noncomputable def finiteSignFlip (i : ι) : (ι → Bool) ≃ (ι → Bool) := by
  classical
  exact { toFun := fun ε j => if j = i then !(ε j) else ε j
          invFun := fun ε j => if j = i then !(ε j) else ε j
          left_inv := by intro ε; funext j; by_cases hj : j = i <;> simp [hj]
          right_inv := by intro ε; funext j; by_cases hj : j = i <;> simp [hj] }

theorem finiteSignFlip_same (i : ι) (ε : ι → Bool) : finiteSignFlip i ε i = !(ε i) := by
  classical
  simp [finiteSignFlip]

theorem finiteSignFlip_other (i j : ι) (hji : j ≠ i) (ε : ι → Bool) :
    finiteSignFlip i ε j = ε j := by
  classical
  simp [finiteSignFlip, hji]

variable [Fintype ι] [DecidableEq ι]

theorem finiteSign_expect_mul_ne (i j : ι) (hij : i ≠ j) :
    (𝔼 ε : ι → Bool, finiteSign (ε i) * finiteSign (ε j)) = 0 := by
  have he : (𝔼 ε : ι → Bool, finiteSign (ε i) * finiteSign (ε j)) =
      -(𝔼 ε : ι → Bool, finiteSign (ε i) * finiteSign (ε j)) := by
    calc
      _ = 𝔼 ε : ι → Bool, -(finiteSign (ε i) * finiteSign (ε j)) := by
        apply Fintype.expect_equiv (finiteSignFlip i)
        intro ε
        simp only [finiteSignFlip_same, finiteSignFlip_other i j hij.symm,
          finiteSign_not, neg_mul, neg_neg]
      _ = _ := Finset.expect_neg_distrib _ _
  linarith

theorem finiteSign_expect_mul (i j : ι) :
    (𝔼 ε : ι → Bool, finiteSign (ε i) * finiteSign (ε j)) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [← pow_two, finiteSign_sq, Fintype.expect_const, ite_true]
  · simp only [finiteSign_expect_mul_ne i j hij, ite_eq_right hij]

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

noncomputable def finiteSignSum (v : ι → E) (ε : ι → Bool) : E :=
  ∑ i, finiteSign (ε i) • v i

omit [DecidableEq ι] in
theorem finiteSignSum_map (T : E →ₗ[ℝ] F) (v : ι → E) (ε : ι → Bool) :
    T (finiteSignSum v ε) = finiteSignSum (fun i => T (v i)) ε := by
  simp only [finiteSignSum, map_sum, map_smul]

omit [DecidableEq ι] in
theorem finiteSignSum_sub (v w : ι → E) (ε : ι → Bool) :
    finiteSignSum v ε - finiteSignSum w ε = finiteSignSum (fun i => v i - w i) ε := by
  simp only [finiteSignSum, smul_sub, Finset.sum_sub_distrib]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [DecidableEq ι] in
theorem finiteSignSum_norm_sq (v : ι → H) (ε : ι → Bool) :
    ‖finiteSignSum v ε‖ ^ 2 = ∑ i, ∑ j,
      (finiteSign (ε i) * finiteSign (ε j)) * inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq, finiteSignSum]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (v j) (v i)]

theorem finiteSignSum_expect_norm_sq (v : ι → H) :
    (𝔼 ε : ι → Bool, ‖finiteSignSum v ε‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  classical
  simp only [finiteSignSum_norm_sq, Finset.expect_sum_comm, ← Finset.expect_mul,
    finiteSign_expect_mul]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, real_inner_self_eq_norm_sq]

end ThomGame.Analysis
