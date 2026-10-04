module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-! Measurable centered representatives and genuine integer shears on the two-torus. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open Set MeasureTheory

abbrev Circle := AddCircle (1 : ℝ)
abbrev Torus := Circle × Circle

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def rep (x : Circle) : ℝ := (AddCircle.equivIco 1 (-(1 / 2 : ℝ)) x).val

theorem rep_mem (x : Circle) : rep x ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := by
  have h := (AddCircle.equivIco 1 (-(1 / 2 : ℝ)) x).property
  norm_num at h ⊢
  exact h

theorem rep_abs_le (x : Circle) : |rep x| ≤ 1 / 2 :=
  abs_le.mpr ⟨(rep_mem x).1, (rep_mem x).2.le⟩

theorem rep_measurable : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) (-(1 / 2 : ℝ))).measurable

theorem coe_rep (x : Circle) : (rep x : Circle) = x := AddCircle.coe_equivIco

theorem rep_coe {x : ℝ} (hx : x ∈ Ico (-(1 / 2 : ℝ)) (1 / 2)) : rep (x : Circle) = x := by
  apply AddCircle.equivIco_coe_of_mem
  norm_num
  exact hx

@[simp] theorem rep_zero : rep 0 = 0 := rep_coe (by norm_num)

theorem rep_eq_zero_iff (x : Circle) : rep x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    rw [← coe_rep x, hx]
    rfl
  · rintro rfl
    exact rep_zero

def pointRep (x : Torus) : ℝ × ℝ := (rep x.1, rep x.2)

def ofReal (x : ℝ × ℝ) : Torus := ((x.1 : Circle), (x.2 : Circle))

theorem ofReal_pointRep (x : Torus) : ofReal (pointRep x) = x := Prod.ext (coe_rep x.1) (coe_rep x.2)

theorem pointRep_ofReal (x : ℝ × ℝ)
    (hx : x.1 ∈ Ico (-(1 / 2 : ℝ)) (1 / 2)) (hy : x.2 ∈ Ico (-(1 / 2 : ℝ)) (1 / 2)) :
    pointRep (ofReal x) = x := Prod.ext (rep_coe hx) (rep_coe hy)

theorem pointRep_eq_zero_iff (x : Torus) : pointRep x = 0 ↔ x = 0 := by
  simp only [pointRep, Prod.mk_eq_zero, rep_eq_zero_iff]
  exact Prod.mk_eq_zero.symm

def lower (k : ℤ) : Torus ≃ₜ Torus where
  toFun x := (x.1, k • x.1 + x.2)
  invFun x := (x.1, -k • x.1 + x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def upper (k : ℤ) : Torus ≃ₜ Torus where
  toFun x := (k • x.2 + x.1, x.2)
  invFun x := (-k • x.2 + x.1, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem lower_ofReal (k : ℤ) (x : ℝ × ℝ) :
    lower k (ofReal x) = ofReal (x.1, (k : ℝ) * x.1 + x.2) := by
  apply Prod.ext
  · rfl
  · change k • (x.1 : Circle) + (x.2 : Circle) = (((k : ℝ) * x.1 + x.2 : ℝ) : Circle)
    rw [← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul]

theorem upper_ofReal (k : ℤ) (x : ℝ × ℝ) :
    upper k (ofReal x) = ofReal ((k : ℝ) * x.2 + x.1, x.2) := by
  apply Prod.ext
  · change k • (x.2 : Circle) + (x.1 : Circle) = (((k : ℝ) * x.2 + x.1 : ℝ) : Circle)
    rw [← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul]
  · rfl

end ThomGame.Analysis.IntegerTorus
