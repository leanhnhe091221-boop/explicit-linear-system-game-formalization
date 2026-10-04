module

public import ThomGame.Analysis.FiniteNoDriftMarkovComm

/-! Explicit root-energy transport through a finite number of shear heat steps. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem finiteNoDrift_shear_markov_comm (f : Compressor.Generator → UnitaryMatrix d) {δ a : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (hδa : δ ≤ a)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hroot : ∀ r m, finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (r : Compressor.Root) (m : Compressor.Coeff) :
    finiteNoDriftComm (f (.inl (r, m))) (matrixLazyMarkov (finiteNoDriftShearTuple f) X) ≤ 4 * a := by
  have ha : 0 ≤ a := hδ.trans hδa
  have ht := finiteNoDriftComm_markov (f (.inl (r, m))) (finiteNoDriftShearTuple f) X (hroot r m)
    (b := 4 * a + 2 * δ) (fun j => by
      let s := (Fintype.equivFinOfCardEq Compressor.root_card).symm j
      constructor
      · have hh := finiteNoDrift_signed_pullback_comm f hf ha X hX hroot s r m false
        simpa only [Bool.false_eq_true, ↓reduceIte, inv_inv, s, finiteNoDriftShearTuple] using hh
      · have hh := finiteNoDrift_signed_pullback_comm f hf ha X hX hroot s r m true
        simpa only [↓reduceIte, s, finiteNoDriftShearTuple] using hh)
  linarith

theorem finiteNoDrift_shear_heat_comm (f : Compressor.Generator → UnitaryMatrix d) {δ a : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hroot : ∀ r m, finiteNoDriftComm (f (.inl (r, m))) X ≤ a) (M : Nat) :
    ∀ r m, finiteNoDriftComm (f (.inl (r, m))) ((matrixLazyMarkov (finiteNoDriftShearTuple f) ^ M) X) ≤
      (4 : ℝ) ^ M * (a + δ) := by
  induction M with
  | zero =>
    intro r m
    have hr := hroot r m
    simp only [pow_zero, Module.End.one_apply, one_mul]
    linarith
  | succ M ih =>
    intro r m
    have hp : 1 ≤ (4 : ℝ) ^ M := one_le_pow₀ (by norm_num)
    have hda : δ ≤ (4 : ℝ) ^ M * (a + δ) := by nlinarith
    have hy : matrixOpNorm ((matrixLazyMarkov (finiteNoDriftShearTuple f) ^ M) X) ≤ 1 :=
      (matrixLazyMarkov_pow_matrixOpNorm_le (finiteNoDriftShearTuple f) M X).trans hX
    have ht := finiteNoDrift_shear_markov_comm f hf hδ hda _ hy ih r m
    rw [pow_succ', Module.End.mul_apply]
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using ht

theorem finiteNoDrift_root_heat_transport (f : Compressor.Generator → UnitaryMatrix d) {δ b : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hN : Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X) ≤ b)
    (M : Nat) :
    Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient)
      ((matrixLazyMarkov (finiteNoDriftShearTuple f) ^ M) X)) ≤
      14 * (4 : ℝ) ^ M * (8 * Real.sqrt 234375 * b + 3 * δ) := by
  have hroot := finiteNoDrift_full_initial_comm f hf hδ hb X hX hN
  have hh := finiteNoDrift_shear_heat_comm f hf hδ (by positivity : 0 ≤ 8 * Real.sqrt 234375 * b + 2 * δ)
    X hX hroot M
  have he := finiteNoDriftRootEnergy_max f finiteNoDriftCoefficient
    ((matrixLazyMarkov (finiteNoDriftShearTuple f) ^ M) X)
    (by positivity : 0 ≤ (4 : ℝ) ^ M * ((8 * Real.sqrt 234375 * b + 2 * δ) + δ))
    (fun c i => hh (Compressor.cyclicRoot c) (finiteNoDriftCoefficient i))
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at he
  convert he using 1 <;> ring

end ThomGame.Analysis
