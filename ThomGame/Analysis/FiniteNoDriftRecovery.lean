module

public import ThomGame.Analysis.FiniteNoDriftCompressor

/-! The six shears and negative-label recovery give the original anchored bound. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {d : Nat}

noncomputable def finiteNoDriftShearTuple (f : Compressor.Generator → UnitaryMatrix d) :
    Fin 6 → UnitaryMatrix d := fun j => f (.inr ((Fintype.equivFinOfCardEq Compressor.root_card).symm j))

theorem finiteNoDriftShearTuple_at (f : Compressor.Generator → UnitaryMatrix d) (s : Compressor.Root) :
    finiteNoDriftShearTuple f ((Fintype.equivFinOfCardEq Compressor.root_card) s) = f (.inr s) := by
  simp only [finiteNoDriftShearTuple, Equiv.symm_apply_apply]

abbrev FiniteNoDriftQIndex := (Fin 2 × Fin 234375) ⊕ (Fin 78125 × Fin 6)

theorem finiteNoDriftQIndex_card : Fintype.card FiniteNoDriftQIndex = 937500 := by
  simp [FiniteNoDriftQIndex, Fintype.card_sum, Fintype.card_prod]

noncomputable def finiteNoDriftQAt (f : Compressor.Generator → UnitaryMatrix d) :
    FiniteNoDriftQIndex → UnitaryMatrix d
  | .inl p => finiteNoDriftRootTuple f finiteNoDriftCoefficient p.2
  | .inr p => finiteNoDriftShearTuple f p.2

noncomputable def finiteNoDriftQTuple (f : Compressor.Generator → UnitaryMatrix d) :
    Fin 937500 → UnitaryMatrix d := fun j =>
  finiteNoDriftQAt f ((Fintype.equivFinOfCardEq finiteNoDriftQIndex_card).symm j)

set_option maxRecDepth 4096 in
theorem finiteNoDriftQEnergy (f : Compressor.Generator → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy (finiteNoDriftQTuple f) X =
      (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X +
        matrixCoordinateEnergy (finiteNoDriftShearTuple f) X) / 2 := by
  have hsum : (∑ j : Fin 937500, finiteNoDriftComm (finiteNoDriftQTuple f j) X ^ 2) =
      ∑ p : FiniteNoDriftQIndex, finiteNoDriftComm (finiteNoDriftQAt f p) X ^ 2 :=
    Equiv.sum_comp (Fintype.equivFinOfCardEq finiteNoDriftQIndex_card).symm
      (fun p : FiniteNoDriftQIndex => finiteNoDriftComm (finiteNoDriftQAt f p) X ^ 2)
  rw [Fintype.sum_sum_type] at hsum
  simp only [Fintype.sum_prod_type, finiteNoDriftQAt, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold matrixCoordinateEnergy
  change lazyMarkovWeight 937500 * (∑ j, finiteNoDriftComm (finiteNoDriftQTuple f j) X ^ 2) =
    (lazyMarkovWeight 234375 * (∑ j : Fin 234375, finiteNoDriftComm (finiteNoDriftRootTuple f finiteNoDriftCoefficient j) X ^ 2) +
      lazyMarkovWeight 6 * (∑ j : Fin 6, finiteNoDriftComm (finiteNoDriftShearTuple f j) X ^ 2)) / 2
  rw [hsum]
  norm_num only [lazyMarkovWeight, Nat.cast_ofNat, Nat.reduceMul, Nat.reducePow]
  ring

theorem finiteNoDrift_recovery_comm (f : Compressor.Generator → UnitaryMatrix d)
    (X : CMatrix d) {b : ℝ} (hs : ∀ s, finiteNoDriftComm (f (.inr s)) X ≤ b) (c : Compressor.Axis) :
    finiteNoDriftComm (Word.eval f (Compressor.recoveryWord c)) X ≤ 6 * b := by
  let S := f (.inr (Compressor.cyclicRoot c))
  let T := f (.inr (Compressor.reverse (Compressor.cyclicRoot c)))
  have he : Word.eval f (Compressor.recoveryWord c) = (S * T⁻¹ * S) * (S * T⁻¹ * S) := by
    simp [Compressor.recoveryWord, Compressor.power, Compressor.shear, S, T, mul_assoc]
  rw [he]
  have h₁ := finiteNoDriftComm_mul S T⁻¹ X
  have h₂ := finiteNoDriftComm_mul (S * T⁻¹) S X
  have h₃ := finiteNoDriftComm_mul (S * T⁻¹ * S) (S * T⁻¹ * S) X
  rw [finiteNoDriftComm_inv] at h₁
  have hS := hs (Compressor.cyclicRoot c)
  have hT := hs (Compressor.reverse (Compressor.cyclicRoot c))
  change finiteNoDriftComm S X ≤ b at hS
  change finiteNoDriftComm T X ≤ b at hT
  linarith

variable [NeZero d]

theorem finiteNoDrift_all_root_comm (f : Compressor.Generator → UnitaryMatrix d) {δ a b : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hpos : ∀ r m, Compressor.positive (.inl (r, m)) = true → finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (hs : ∀ s, finiteNoDriftComm (f (.inr s)) X ≤ b) (r : Compressor.Root) (m : Compressor.Coeff) :
    finiteNoDriftComm (f (.inl (r, m))) X ≤ a + 12 * b + 2 * δ := by
  cases m with
  | none => have hp := hpos r none rfl; linarith
  | some p =>
    rcases p with ⟨c, v⟩
    cases v
    · have he := finiteNoDrift_recovery_dist f hf c r
      rw [unitaryDist_comm] at he
      have ht := finiteNoDriftComm_close (f (.inl (r, some (c, false))))
        (Word.eval f (Compressor.recoveryWord c) * f (.inl (r, some (c, true))) *
          (Word.eval f (Compressor.recoveryWord c))⁻¹) X hX
      have hc := finiteNoDriftComm_conj (Word.eval f (Compressor.recoveryWord c))
        (f (.inl (r, some (c, true)))) X
      have hp := hpos r (some (c, true)) rfl
      have hr := finiteNoDrift_recovery_comm f X hs c
      linarith
    · have hp := hpos r (some (c, true)) rfl; linarith

theorem finiteNoDrift_Q_anchor_energy (f : Compressor.Generator → UnitaryMatrix d) {δ a b : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hpos : ∀ r m, Compressor.positive (.inl (r, m)) = true → finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (hs : ∀ s, finiteNoDriftComm (f (.inr s)) X ≤ b) :
    Real.sqrt (matrixCoordinateEnergy (finiteNoDriftQTuple f) X) ≤ 14 * a + (337 / 2) * b + 28 * δ := by
  have hN := finiteNoDriftRootEnergy_max f finiteNoDriftCoefficient X
    (by positivity : 0 ≤ a + 12 * b + 2 * δ)
    (fun c i => finiteNoDrift_all_root_comm f hf hδ hb X hX hpos hs _ _)
  have hS := finiteNoDriftEnergy_max (finiteNoDriftShearTuple f) X hb
    (fun j => hs ((Fintype.equivFinOfCardEq Compressor.root_card).symm j))
  have hN0 := matrixCoordinateEnergy_nonneg (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X
  have hS0 := matrixCoordinateEnergy_nonneg (finiteNoDriftShearTuple f) X
  have hsum : Real.sqrt ((matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X +
      matrixCoordinateEnergy (finiteNoDriftShearTuple f) X) / 2) ≤
      Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X) +
      Real.sqrt (matrixCoordinateEnergy (finiteNoDriftShearTuple f) X) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hN0, Real.sq_sqrt hS0,
        Real.sqrt_nonneg (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X),
        Real.sqrt_nonneg (matrixCoordinateEnergy (finiteNoDriftShearTuple f) X)]
  rw [finiteNoDriftQEnergy]
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at hN
  linarith

end ThomGame.Analysis
