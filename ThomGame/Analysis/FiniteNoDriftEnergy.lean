module

public import ThomGame.Analysis.FiniteNoDriftRootWords

/-! Explicit normalized energy estimates for finite tuples. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {d h : Nat} [NeZero h]

theorem finiteNoDriftEnergy_max (U : Fin h → UnitaryMatrix d) (X : CMatrix d)
    {a : ℝ} (ha : 0 ≤ a) (hcomm : ∀ j, finiteNoDriftComm (U j) X ≤ a) :
    Real.sqrt (matrixCoordinateEnergy U X) ≤ a / 2 := by
  have hs : ∑ j, hsNorm ((U j).val * X - X * (U j).val) ^ 2 ≤ (h : ℝ) * a ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin h, a ^ 2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (finiteNoDriftComm_nonneg (U j) X) (hcomm j) 2)
      _ = _ := by simp
  have he := mul_le_mul_of_nonneg_left hs (lazyMarkovWeight_nonneg h)
  have hw := lazyMarkovWeight_mul_card h
  have hb : matrixCoordinateEnergy U X ≤ a ^ 2 / 4 := by
    change matrixCoordinateEnergy U X ≤ lazyMarkovWeight h * ((h : ℝ) * a ^ 2) at he
    rw [← mul_assoc, hw] at he
    linarith
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, by nlinarith⟩

theorem finiteNoDriftEnergy_single (U : Fin h → UnitaryMatrix d) (X : CMatrix d) (j : Fin h) :
    finiteNoDriftComm (U j) X ^ 2 ≤ (4 * h : ℝ) * matrixCoordinateEnergy U X := by
  have hs : finiteNoDriftComm (U j) X ^ 2 ≤ ∑ l, finiteNoDriftComm (U l) X ^ 2 :=
    Finset.single_le_sum (f := fun l : Fin h => finiteNoDriftComm (U l) X ^ 2)
      (fun l _ => sq_nonneg (finiteNoDriftComm (U l) X)) (Finset.mem_univ j)
  have he := mul_le_mul_of_nonneg_left hs (lazyMarkovWeight_nonneg h)
  have he' : lazyMarkovWeight h * finiteNoDriftComm (U j) X ^ 2 ≤ matrixCoordinateEnergy U X := he
  have hcard : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
  calc
    _ = (4 * h : ℝ) * (lazyMarkovWeight h * finiteNoDriftComm (U j) X ^ 2) := by
      unfold lazyMarkovWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left he' (by positivity)

theorem finiteNoDriftEnergy_sq_bound (U : Fin h → UnitaryMatrix d) (X : CMatrix d)
    {τ : ℝ} (hτ : Real.sqrt (matrixCoordinateEnergy U X) ≤ τ) : matrixCoordinateEnergy U X ≤ τ ^ 2 := by
  have hs := Real.sq_sqrt (matrixCoordinateEnergy_nonneg U X)
  nlinarith [Real.sqrt_nonneg (matrixCoordinateEnergy U X)]

theorem finiteNoDriftRootEnergy_max {r : Nat} (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (X : CMatrix d) {a : ℝ} (ha : 0 ≤ a)
    (hroot : ∀ c i, finiteNoDriftComm (f (.inl (Compressor.cyclicRoot c, σ i))) X ≤ a) :
    Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f σ) X) ≤ (2 * r : Nat) * a := by
  letI : NeZero (3 * 5 ^ r) := ⟨by positivity⟩
  have hh := finiteNoDriftEnergy_max (finiteNoDriftRootTuple f σ) X (by positivity : 0 ≤ (4 * r : Nat) * a)
    (finiteNoDriftRootTuple_comm f σ X ha hroot)
  convert hh using 1 <;> push_cast <;> ring

end ThomGame.Analysis
