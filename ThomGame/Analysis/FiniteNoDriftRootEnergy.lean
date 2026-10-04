module

public import ThomGame.Analysis.FiniteNoDriftEnergy

/-! The positive root tuple embeds in the full root tuple with the exact factor 125. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {d : Nat}

theorem finiteNoDriftRootEnergy_formula {r : Nat} (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (X : CMatrix d) :
    matrixCoordinateEnergy (finiteNoDriftRootTuple f σ) X = lazyMarkovWeight (3 * 5 ^ r) *
      ∑ p : FiniteNoDriftRootIndex r, finiteNoDriftComm (Word.eval f (finiteNoDriftRootWord σ p.1 p.2)) X ^ 2 := by
  unfold matrixCoordinateEnergy
  congr 1
  exact (Equiv.sum_comp (Fintype.equivFinOfCardEq (finiteNoDriftRootIndex_card r)).symm
    (fun p => finiteNoDriftComm (Word.eval f (finiteNoDriftRootWord σ p.1 p.2)) X ^ 2))

theorem finiteNoDrift_positive_energy_le (f : Compressor.Generator → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X ≤
      125 * matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X := by
  classical
  let e : FiniteNoDriftRootIndex 4 → FiniteNoDriftRootIndex 7 := fun p => (p.1, finiteNoDriftRootExtend p.2)
  have heinj : Function.Injective e := by
    intro p q hpq
    have hpair : p.1 = q.1 ∧ finiteNoDriftRootExtend p.2 = finiteNoDriftRootExtend q.2 := Prod.mk.inj hpq
    exact Prod.ext hpair.1 (finiteNoDriftRootExtend_injective hpair.2)
  let g := fun p : FiniteNoDriftRootIndex 7 =>
    finiteNoDriftComm (Word.eval f (finiteNoDriftRootWord finiteNoDriftCoefficient p.1 p.2)) X ^ 2
  have hs : (∑ p : FiniteNoDriftRootIndex 4, g (e p)) ≤ ∑ p : FiniteNoDriftRootIndex 7, g p := by
    calc
      _ = ∑ p ∈ Finset.univ.image e, g p := (Finset.sum_image (fun _ _ _ _ he => heinj he)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun p _ _ => sq_nonneg _)
  have he (p : FiniteNoDriftRootIndex 4) : g (e p) =
      finiteNoDriftComm (Word.eval f (finiteNoDriftRootWord finiteNoDriftPositiveCoefficient p.1 p.2)) X ^ 2 := by
    dsimp only [g, e]
    rw [finiteNoDriftRootWord_extend]
  simp only [he] at hs
  have hw : lazyMarkovWeight (3 * 5 ^ 4) = 125 * lazyMarkovWeight (3 * 5 ^ 7) := by
    norm_num [lazyMarkovWeight]
  rw [finiteNoDriftRootEnergy_formula, finiteNoDriftRootEnergy_formula]
  calc
    _ ≤ lazyMarkovWeight (3 * 5 ^ 4) * ∑ p : FiniteNoDriftRootIndex 7, g p :=
      mul_le_mul_of_nonneg_left hs (lazyMarkovWeight_nonneg _)
    _ = _ := by rw [hw]; dsimp only [g]; ring

theorem finiteNoDrift_positive_cyclic_comm (f : Compressor.Generator → UnitaryMatrix d)
    (X : CMatrix d) {τ : ℝ} (hτ : 0 ≤ τ)
    (hE : Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X) ≤ τ)
    (c : Fin 3) (i : Fin 4) :
    finiteNoDriftComm (f (.inl (Compressor.cyclicRoot c, finiteNoDriftPositiveCoefficient i))) X ≤ (175 / 2) * τ := by
  obtain ⟨j, hj⟩ := finiteNoDriftRootTuple_generator f finiteNoDriftPositiveCoefficient c i
  have hs := finiteNoDriftEnergy_single (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X j
  rw [hj] at hs
  have he := finiteNoDriftEnergy_sq_bound (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X hE
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.cast_ofNat] at hs
  nlinarith [finiteNoDriftComm_nonneg (f (.inl (Compressor.cyclicRoot c, finiteNoDriftPositiveCoefficient i))) X]

end ThomGame.Analysis
