module

public import ThomGame.Analysis.FiniteUCPWeakGapHeat
public import ThomGame.Analysis.MatrixChannelEnergySeminorm

/-! The actual UCP heat sandwich and its two ALT smoothing estimates. The
root-word transport estimate is an explicit separate input. -/

@[expose] public section
namespace ThomGame.Analysis
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : ℕ}

noncomputable def finiteUCPCompose (P Q : CMatrix d →CP CMatrix d) :
    CMatrix d →CP CMatrix d where
  toLinearMap := P.toLinearMap.comp Q.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have he : M.map (P.toLinearMap.comp Q.toLinearMap) =
        (M.map Q.toLinearMap).map P.toLinearMap := by ext i j; rfl
    rw [he]
    exact P.map_cstarMatrix_nonneg' k _ (Q.map_cstarMatrix_nonneg' k M hM)

@[simp] theorem finiteUCPCompose_apply (P Q : CMatrix d →CP CMatrix d) (X : CMatrix d) :
    finiteUCPCompose P Q X = P (Q X) := rfl

noncomputable def finiteUCPSandwich (P Q : CMatrix d →CP CMatrix d) :
    CMatrix d →CP CMatrix d := finiteUCPCompose P (finiteUCPCompose Q P)

@[simp] theorem finiteUCPSandwich_apply (P Q : CMatrix d →CP CMatrix d) (X : CMatrix d) :
    finiteUCPSandwich P Q X = P (Q (P X)) := rfl

theorem finiteUCPSandwich_one (P Q : CMatrix d →CP CMatrix d)
    (hP : P 1 = 1) (hQ : Q 1 = 1) : finiteUCPSandwich P Q 1 = 1 := by
  simp only [finiteUCPSandwich_apply, hP, hQ]

theorem finiteUCPSandwich_trace (P Q : CMatrix d →CP CMatrix d)
    (hP : ∀ X, normalizedTrace (P X) = normalizedTrace X)
    (hQ : ∀ X, normalizedTrace (Q X) = normalizedTrace X) (X : CMatrix d) :
    normalizedTrace (finiteUCPSandwich P Q X) = normalizedTrace X := by
  simp only [finiteUCPSandwich_apply, hP, hQ]

variable [NeZero d]

omit [NeZero d] in
theorem finiteUCPSandwich_displacement (P Q : CMatrix d →CP CMatrix d)
    (hP : P 1 = 1) (hQ : Q 1 = 1)
    (htP : ∀ X, normalizedTrace (P X) = normalizedTrace X)
    (htQ : ∀ X, normalizedTrace (Q X) = normalizedTrace X) (X : CMatrix d) :
    hsNorm (X - finiteUCPSandwich P Q X) ≤
      2 * hsNorm (X - P X) + hsNorm (X - Q X) := by
  have he : X - finiteUCPSandwich P Q X =
      (X - P X) + P (X - Q X) + P (Q (X - P X)) := by
    simp only [finiteUCPSandwich_apply, map_sub]
    abel
  have hm := matrixUCP_hsNorm_le P hP htP (X - Q X)
  have hl := (matrixUCP_hsNorm_le P hP htP (Q (X - P X))).trans
    (matrixUCP_hsNorm_le Q hQ htQ (X - P X))
  rw [he]
  have ht := hsNorm_add_le ((X - P X) + P (X - Q X)) (P (Q (X - P X)))
  have ht' := hsNorm_add_le (X - P X) (P (X - Q X))
  linarith

variable {h : ℕ} [NeZero h]

theorem finiteUCP_coordinateEnergy_eq_channel (U : Fin h → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy U X = matrixChannelEnergy (matrixLazyMarkov U) X := by
  rw [matrixCoordinateEnergy, ← matrixLazyMarkov_energy, mul_sub, normalizedTrace_sub,
    Complex.sub_re, normalizedTrace_gram, Complex.ofReal_re]
  rfl

theorem finiteUCP_coordinateEnergy_sqrt_add (U : Fin h → UnitaryMatrix d) (X Y : CMatrix d) :
    Real.sqrt (matrixCoordinateEnergy U (X + Y)) ≤
      Real.sqrt (matrixCoordinateEnergy U X) + Real.sqrt (matrixCoordinateEnergy U Y) := by
  simp only [finiteUCP_coordinateEnergy_eq_channel]
  exact matrixUCP_energy_sqrt_add_le (matrixLazyMarkovCP U)
    (matrixLazyMarkov_one U) (matrixLazyMarkov_trace U) X Y

theorem finiteUCP_coordinateEnergy_sqrt_transfer (U : Fin h → UnitaryMatrix d) (X Y : CMatrix d) :
    Real.sqrt (matrixCoordinateEnergy U X) ≤
      Real.sqrt (matrixCoordinateEnergy U Y) + hsNorm (X - Y) := by
  have ht := finiteUCP_coordinateEnergy_sqrt_add U Y (X - Y)
  rw [show Y + (X - Y) = X by abel] at ht
  exact ht.trans (add_le_add (le_refl _) (matrixCoordinateEnergy_sqrt_le_hsNorm U (X - Y)))

theorem finiteUCP_sandwich_distance_scalar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    240 * Real.sqrt a + 288 * Real.sqrt b ≤ 600 * Real.sqrt ((a + b) / 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ (a + b) / 2 by positivity)
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hd := sq_nonneg (288 * Real.sqrt a - 240 * Real.sqrt b)
  have hn := Real.sqrt_nonneg ((a + b) / 2)
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

theorem finiteUCP_sandwich_energy_scalar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((a + b) / 2) ≤ Real.sqrt a + Real.sqrt b := by
  have hs := Real.sq_sqrt (show 0 ≤ (a + b) / 2 by positivity)
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg ((a + b) / 2),
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

variable {hN hS hQ : ℕ} [NeZero hN] [NeZero hS] [NeZero hQ]

/-- The Q smoothing bridge, with the root-word transport term `R` displayed.
The maps are concrete powers of the N and S lazy Markov channels. -/
theorem finiteUCP_heatSandwich_defectControl
    (N : Fin hN → UnitaryMatrix d) (S : Fin hS → UnitaryMatrix d)
    (Q : Fin hQ → UnitaryMatrix d) (L M : ℕ)
    (hQenergy : ∀ X, matrixCoordinateEnergy Q X =
      (matrixCoordinateEnergy N X + matrixCoordinateEnergy S X) / 2)
    {νN νS bN bS R β : ℝ}
    (hNdist : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - (matrixLazyMarkov N ^ L) X) ≤
      120 * Real.sqrt (matrixCoordinateEnergy N X) + νN)
    (hSdist : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - (matrixLazyMarkov S ^ M) X) ≤
      288 * Real.sqrt (matrixCoordinateEnergy S X) + νS)
    (hNenergy : ∀ X, matrixOpNorm X ≤ 1 →
      Real.sqrt (matrixCoordinateEnergy N ((matrixLazyMarkov N ^ L) X)) ≤ bN)
    (hSenergy : ∀ X, matrixOpNorm X ≤ 1 →
      Real.sqrt (matrixCoordinateEnergy S ((matrixLazyMarkov S ^ M) X)) ≤ bS)
    (htransport : ∀ X, matrixOpNorm X ≤ 1 →
      Real.sqrt (matrixCoordinateEnergy N ((matrixLazyMarkov S ^ M) ((matrixLazyMarkov N ^ L) X))) ≤ R)
    (hβ : 0 ≤ β) (hβdist : 2 * νN + νS ≤ β)
    (hβenergy : bN + bS + 120 * R + νN ≤ β) :
    FiniteUCPDefectControl Q
      (finiteUCPSandwich (matrixMarkovPowerCP N L) (matrixMarkovPowerCP S M)).toLinearMap
      (1 / 360000) β := by
  let P := matrixMarkovPowerCP N L
  let F := matrixMarkovPowerCP S M
  have hP : P 1 = 1 := matrixLazyMarkov_pow_one N L
  have hF : F 1 = 1 := matrixLazyMarkov_pow_one S M
  have htP : ∀ X, normalizedTrace (P X) = normalizedTrace X := matrixLazyMarkov_pow_trace N L
  have htF : ∀ X, normalizedTrace (F X) = normalizedTrace X := matrixLazyMarkov_pow_trace S M
  refine ⟨hβ, ?_, ?_⟩
  · intro X hX
    have hd := finiteUCPSandwich_displacement P F hP hF htP htF X
    have hn := hNdist X hX
    have hs := hSdist X hX
    have hc := finiteUCP_sandwich_distance_scalar
      (matrixCoordinateEnergy_nonneg N X) (matrixCoordinateEnergy_nonneg S X)
    rw [← hQenergy X] at hc
    have hroot : (Real.sqrt (1 / 360000 : ℝ))⁻¹ = 600 := by
      rw [show (1 / 360000 : ℝ) = (1 / 600 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 600)]
      norm_num
    rw [hroot]
    change hsNorm (X - finiteUCPSandwich P F X) ≤ _
    change hsNorm (X - P X) ≤ _ at hn
    change hsNorm (X - F X) ≤ _ at hs
    linarith
  · intro X hX
    let z := F (P X)
    have hPX : matrixOpNorm (P X) ≤ 1 := (matrixLazyMarkov_pow_matrixOpNorm_le N L X).trans hX
    have hz : matrixOpNorm z ≤ 1 := (matrixLazyMarkov_pow_matrixOpNorm_le S M (P X)).trans hPX
    have hn := hNenergy z hz
    have hs := hSenergy (P X) hPX
    have hd := hNdist z hz
    have ht := htransport X hX
    have hxfer := finiteUCP_coordinateEnergy_sqrt_transfer S (P z) z
    rw [hsNorm_sub_comm] at hxfer
    have hc := finiteUCP_sandwich_energy_scalar
      (matrixCoordinateEnergy_nonneg N (P z)) (matrixCoordinateEnergy_nonneg S (P z))
    rw [← hQenergy (P z)] at hc
    change Real.sqrt (matrixCoordinateEnergy Q (P z)) ≤ _
    change Real.sqrt (matrixCoordinateEnergy N (P z)) ≤ bN at hn
    change Real.sqrt (matrixCoordinateEnergy S z) ≤ bS at hs
    change hsNorm (z - P z) ≤ 120 * Real.sqrt (matrixCoordinateEnergy N z) + νN at hd
    change Real.sqrt (matrixCoordinateEnergy N z) ≤ R at ht
    linarith

end ThomGame.Analysis
