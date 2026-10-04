module

public import ThomGame.Analysis.IntegerTorusPacking

/-! Propagation of Borel-set measure errors from the two unit shears to their powers. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open Set MeasureTheory

def integerShear (vertical : Bool) (k : ℤ) : Torus ≃ₜ Torus :=
  if vertical then upper k else lower k

theorem integerShear_zero (b : Bool) (x : Torus) : integerShear b 0 x = x := by
  cases b <;> ext <;> simp [integerShear, lower, upper]

theorem integerShear_add (b : Bool) (m n : ℤ) (x : Torus) :
    integerShear b (m + n) x = integerShear b m (integerShear b n x) := by
  cases b <;> ext <;> simp [integerShear, lower, upper, add_zsmul, add_assoc]

theorem integerShear_nat_succ_image (b : Bool) (n : ℕ) (s : Set Torus) :
    integerShear b (n + 1 : ℕ) '' s =
      integerShear b n '' (integerShear b 1 '' s) := by
  rw [Set.image_image]
  congr 1
  funext x
  simp only [Nat.cast_add, Nat.cast_one, integerShear_add]

theorem integerShear_measure_error (μ : Measure Torus) (b : Bool) (ε : ℝ)
    (hmove : ∀ s : Set Torus, MeasurableSet s →
      μ.real s ≤ μ.real (integerShear b 1 '' s) + ε) (n : ℕ)
    (s : Set Torus) (hs : MeasurableSet s) :
    μ.real s ≤ μ.real (integerShear b n '' s) + (n : ℝ) * ε := by
  induction n generalizing s with
  | zero =>
      simpa only [Nat.cast_zero, integerShear_zero, Set.image_id', zero_mul, add_zero]
        using le_refl (μ.real s)
  | succ n ih =>
      have hi := ih (integerShear b 1 '' s)
        ((integerShear b 1).measurableEmbedding.measurableSet_image' hs)
      have h := hmove s hs
      rw [integerShear_nat_succ_image, Nat.cast_succ]
      linarith

theorem cone_measure_errors_of_unit_shears (μ : Measure Torus) (ε : ℝ)
    (hmove : ∀ (b : Bool) (s : Set Torus), MeasurableSet s →
      μ.real s ≤ μ.real (integerShear b 1 '' s) + 2 * ε) :
    ∀ i : Bool × Bool, μ.real (cone i.1) ≤
      μ.real (shearMap i '' cone i.1) + 2 * ((shift i.2 : ℤ) : ℝ) * ε := by
  rintro ⟨b, far⟩
  cases far
  · simpa only [shift, Bool.false_eq_true, ↓reduceIte, shearMap, integerShear,
      Nat.cast_ofNat, Int.cast_ofNat, show (3 : ℝ) * (2 * ε) = 2 * 3 * ε by ring]
      using integerShear_measure_error μ b (2 * ε) (hmove b) 3 (cone b) (cone_measurable b)
  · simpa only [shift, ↓reduceIte, shearMap, integerShear,
      Nat.cast_ofNat, Int.cast_ofNat, show (6 : ℝ) * (2 * ε) = 2 * 6 * ε by ring]
      using integerShear_measure_error μ b (2 * ε) (hmove b) 6 (cone b) (cone_measurable b)

end ThomGame.Analysis.IntegerTorus
