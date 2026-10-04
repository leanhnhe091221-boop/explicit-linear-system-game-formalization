module

public import ThomGame.Analysis.IntegerTorusPacking
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Genuine torus characters and a quantitative energy obstruction for torus measures. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open Set MeasureTheory

def character (x : Circle) : ℂ := AddCircle.toCircle x

theorem character_continuous : Continuous character :=
  continuous_induced_dom.comp AddCircle.continuous_toCircle

@[simp] theorem character_zero : character 0 = 1 := by
  simp [character]

theorem character_add (x y : Circle) : character (x + y) = character x * character y := by
  simp [character, AddCircle.toCircle_add]

@[simp] theorem character_norm (x : Circle) : ‖character x‖ = 1 :=
  (AddCircle.toCircle x).norm_coe

theorem character_rep (x : Circle) :
    character x = Complex.exp (Complex.I * ((2 * Real.pi * rep x : ℝ) : ℂ)) := by
  conv_lhs => rw [← coe_rep x]
  simp only [character, AddCircle.toCircle_apply_mk, div_one, _root_.Circle.coe_exp]
  congr 1
  ring

theorem character_chord_lower (x : Circle) : 4 * |rep x| ≤ ‖character x - 1‖ := by
  have hpi := Real.pi_pos
  have hx : |Real.pi * rep x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [rep_abs_le x]
  have hs := Real.mul_abs_le_abs_sin hx
  rw [abs_mul, abs_of_pos hpi] at hs
  have hp : 2 / Real.pi * (Real.pi * |rep x|) = 2 * |rep x| := by
    field_simp
  rw [hp] at hs
  rw [character_rep, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show 2 * Real.pi * rep x / 2 = Real.pi * rep x by ring, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  linarith

theorem character_chord_upper (x : Circle) : ‖character x - 1‖ ≤ 2 := by
  calc
    ‖character x - 1‖ ≤ ‖character x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

def coordinateEnergy (x : Torus) : ℝ :=
  ‖character x.1 - 1‖ ^ 2 + ‖character x.2 - 1‖ ^ 2

theorem coordinateEnergy_nonneg (x : Torus) : 0 ≤ coordinateEnergy x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem coordinateEnergy_continuous : Continuous coordinateEnergy := by
  exact (((character_continuous.comp continuous_fst).sub continuous_const).norm.pow 2).add
    (((character_continuous.comp continuous_snd).sub continuous_const).norm.pow 2)

theorem coordinateEnergy_le_eight (x : Torus) : coordinateEnergy x ≤ 8 := by
  have h₁ := character_chord_upper x.1
  have h₂ := character_chord_upper x.2
  dsimp [coordinateEnergy]
  nlinarith [norm_nonneg (character x.1 - 1), norm_nonneg (character x.2 - 1)]

theorem coordinateEnergy_integrable (μ : Measure Torus) [IsFiniteMeasure μ] :
    Integrable coordinateEnergy μ := by
  apply (integrable_const (8 : ℝ)).mono' coordinateEnergy_continuous.aestronglyMeasurable
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (coordinateEnergy_nonneg x)]
    exact coordinateEnergy_le_eight x

theorem coordinateEnergy_lower_outside {x : Torus} (hx : x ∈ smallSquareᶜ) :
    1 / 16 ≤ coordinateEnergy x := by
  have h₁ := character_chord_lower x.1
  have h₂ := character_chord_lower x.2
  have hn₁ := norm_nonneg (character x.1 - 1)
  have hn₂ := norm_nonneg (character x.2 - 1)
  change ¬ (|rep x.1| ≤ 1 / 16 ∧ |rep x.2| ≤ 1 / 16) at hx
  rw [not_and_or, not_le, not_le] at hx
  dsimp [coordinateEnergy]
  rcases hx with hx | hx
  · nlinarith [sq_nonneg ‖character x.2 - 1‖]
  · nlinarith [sq_nonneg ‖character x.1 - 1‖]

theorem outside_mass_le_energy (μ : Measure Torus) [IsFiniteMeasure μ] :
    μ.real smallSquareᶜ ≤ 16 * ∫ x, coordinateEnergy x ∂μ := by
  have hint := (coordinateEnergy_integrable μ).const_mul (16 : ℝ)
  have hnonneg : 0 ≤ ∫ x, 16 * coordinateEnergy x ∂μ :=
    integral_nonneg fun x => mul_nonneg (by norm_num) (coordinateEnergy_nonneg x)
  have h := hint.measure_le_integral
    (ae_of_all μ fun x => mul_nonneg (by norm_num) (coordinateEnergy_nonneg x))
    (s := smallSquareᶜ) (fun x hx => by nlinarith [coordinateEnergy_lower_outside hx])
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal hnonneg, integral_const_mul] at hr
  exact hr

end ThomGame.Analysis.IntegerTorus
