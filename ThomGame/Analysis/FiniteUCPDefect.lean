module

public import ThomGame.Analysis.MatrixOrthogonalFamilyBounds

/-!
# Finite defect control for an arbitrary linear map

The two estimates in the finite ALT input concern an arbitrary map, which need
not be a power of the tuple's Markov operator or commute with that operator.
The orthogonal-family estimates below only require linearity and these two
uniform estimates. Positivity and preservation of trace enter the subsequent
projection-improvement construction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat}

noncomputable def finiteUCPDefect (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ : ℝ) (X : CMatrix d) : ℝ :=
  max (max (hsNorm (X - Φ X) -
    (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X)) 0)
    (Real.sqrt (matrixCoordinateEnergy U (Φ X)))

/-- The two uniform contraction estimates, with an explicit nonnegative error. -/
structure FiniteUCPDefectControl (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ β : ℝ) : Prop where
  beta_nonneg : 0 ≤ β
  distance : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - Φ X) ≤
    (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) + β
  energy : ∀ X, matrixOpNorm X ≤ 1 →
    Real.sqrt (matrixCoordinateEnergy U (Φ X)) ≤ β

theorem finiteUCPDefectControl_iff (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ β : ℝ) :
    FiniteUCPDefectControl U Φ κ β ↔
      ∀ X, matrixOpNorm X ≤ 1 → finiteUCPDefect U Φ κ X ≤ β := by
  constructor
  · intro h X hX
    apply max_le (max_le ?_ h.beta_nonneg) (h.energy X hX)
    linarith [h.distance X hX]
  · intro h
    have hz := h 0 (by simp [matrixOpNorm])
    have hβ : 0 ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hz)
    refine ⟨hβ, ?_, ?_⟩
    · intro X hX
      have hd : hsNorm (X - Φ X) -
          (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) ≤ β :=
        (le_max_left _ _).trans ((le_max_left _ _).trans (h X hX))
      linarith
    · intro X hX
      exact (le_max_right _ _).trans (h X hX)

def FiniteUCPDistanceBad (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ α : ℝ) (P : CMatrix d) : Prop :=
  IsStarProjection P ∧ P ≠ 0 ∧ α * (normalizedTrace P).re ≤ matrixCoordinateEnergy U P ∧
    2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U P) < hsNorm (P - Φ P)

def FiniteUCPEnergyBad (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (α : ℝ) (P : CMatrix d) : Prop :=
  IsStarProjection P ∧ P ≠ 0 ∧ α ^ 2 * (normalizedTrace P).re / 36 <
    matrixCoordinateEnergy U (Φ P)

variable [NeZero d] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteUCPOrthogonalFamily_bad_energy_bound (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ β : ℝ) (hκ : 0 < κ)
    (hcontrol : FiniteUCPDefectControl U Φ κ β) (P : ι → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (hbad : ∀ i, 2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U (P i)) ≤
      hsNorm (P i - Φ (P i))) :
    (∑ i, matrixCoordinateEnergy U (P i)) ≤ κ * β ^ 2 := by
  have hsE : 0 ≤ ∑ i, matrixCoordinateEnergy U (P i) :=
    Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U _
  have hlow : (2 * (Real.sqrt κ)⁻¹ * Real.sqrt (∑ i, matrixCoordinateEnergy U (P i))) ^ 2 ≤
      ∑ i, hsNorm (P i - Φ (P i)) ^ 2 := by
    calc
      _ = ∑ i, (2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U (P i))) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt hsE, Real.sq_sqrt (matrixCoordinateEnergy_nonneg U _)]
        rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (by positivity) (hsNorm_nonneg _)).2 (hbad i)
  have hlowRoot := Real.le_sqrt_of_sq_le hlow
  have hupper := matrixOrthogonalFamily_distance_bound U Φ P hP horth
    (Real.sqrt κ)⁻¹ β (inv_nonneg.mpr (Real.sqrt_nonneg κ)) hcontrol.beta_nonneg hcontrol.distance
  have hmain : (Real.sqrt κ)⁻¹ * Real.sqrt (∑ i, matrixCoordinateEnergy U (P i)) ≤ β := by
    linarith
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hs : Real.sqrt (∑ i, matrixCoordinateEnergy U (P i)) ≤ β * Real.sqrt κ := by
    apply (div_le_iff₀ hsκ).mp
    simpa only [div_eq_inv_mul] using hmain
  have hs₂ := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hcontrol.beta_nonneg (Real.sqrt_nonneg κ))).2 hs
  simpa only [Real.sq_sqrt hsE, mul_pow, Real.sq_sqrt hκ.le, mul_comm] using hs₂

theorem finiteUCPDistanceBad_family_trace_bound (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ α β : ℝ) (hκ : 0 < κ) (hα : 0 < α)
    (hcontrol : FiniteUCPDefectControl U Φ κ β) (P : ι → CMatrix d)
    (hbad : ∀ i, FiniteUCPDistanceBad U Φ κ α (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    (∑ i, (normalizedTrace (P i)).re) ≤ κ * β ^ 2 / α := by
  have he := finiteUCPOrthogonalFamily_bad_energy_bound U Φ κ β hκ hcontrol P
    (fun i => (hbad i).1) horth (fun i => (hbad i).2.2.2.le)
  have ht : α * (∑ i, (normalizedTrace (P i)).re) ≤ ∑ i, matrixCoordinateEnergy U (P i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hbad i).2.2.1
  apply (le_div_iff₀ hα).2
  linarith

theorem finiteUCPEnergyBad_family_trace_bound (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) (κ α β : ℝ) (hα : 0 < α)
    (hcontrol : FiniteUCPDefectControl U Φ κ β) (P : ι → CMatrix d)
    (hbad : ∀ i, FiniteUCPEnergyBad U Φ α (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    (∑ i, (normalizedTrace (P i)).re) ≤ 36 * β ^ 2 / α ^ 2 := by
  have he := matrixOrthogonalFamily_energy_bound U Φ P (fun i => (hbad i).1) horth β hcontrol.energy
  have ht : α ^ 2 * (∑ i, (normalizedTrace (P i)).re) ≤
      36 * ∑ i, matrixCoordinateEnergy U (Φ (P i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by linarith [(hbad i).2.2.le]
  apply (le_div_iff₀ (sq_pos_of_pos hα)).2
  nlinarith

end ThomGame.Analysis
