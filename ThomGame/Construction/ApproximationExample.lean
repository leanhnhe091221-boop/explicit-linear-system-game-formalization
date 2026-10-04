module

public import ThomGame.Construction.ApproximationReduction
public import ThomGame.Analysis.RankOneInvolution

/-!
# Positive-error assignments need not send the specified J exactly to I

Send every ordinary generator to I and J to diag(-1,1,...,1). All square
and commutation relators hold exactly. An odd row has error 2/sqrt(d).
Thus in every positive tolerance there is an actual approximate
representation of the numbered Sigma presentation with J not equal to I.
This verifies the distinction between asymptotic and literal triviality.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

open Analysis

variable {R C : Type*} (S : SparseSystem R C) (d : Nat) [NeZero d]

def rankOneGeneratorAssignment : Generator C → UnitaryMatrix d
  | none => rankOneUnitary d
  | some _ => 1

def rankOneAssignment : MatrixAssignment (Generator C) d :=
  FreeGroup.lift (rankOneGeneratorAssignment (C := C) d)

theorem rankOneAssignment_relator (tag : RelationTag R C) :
    rankOneAssignment d (FreeGroup.mk (relatorWord S tag)) =
      match tag with
      | .rowEquation r => if S.rhs r = 1 then rankOneUnitary d else 1
      | _ => 1 := by
  change Word.eval (rankOneGeneratorAssignment d) (relatorWord S tag) = _
  cases tag with
  | centralSquare => simp [relatorWord, centralWord, rankOneGeneratorAssignment]
  | variableSquare c => simp [relatorWord, variableWord, rankOneGeneratorAssignment]
  | centralCommutes c => simp [relatorWord, centralWord, variableWord, rankOneGeneratorAssignment]
  | rowCommutes r i j => simp [relatorWord, variableWord, rankOneGeneratorAssignment]
  | rowEquation r =>
    by_cases hb : S.rhs r = 1 <;>
      simp [relatorWord, rowWord, rhsWord, Word.equation, centralWord, variableWord,
        rankOneGeneratorAssignment, hb]

theorem rankOneAssignment_isApprox :
    IsApproxRepresentation (relators S) (2 / Real.sqrt d) (rankOneAssignment d) := by
  have hn : 0 ≤ (2 : ℝ) / Real.sqrt d := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rintro _ ⟨tag, rfl⟩
  rw [rankOneAssignment_relator]
  cases tag with
  | centralSquare => simpa only [unitaryLength_one] using hn
  | variableSquare c => simpa only [unitaryLength_one] using hn
  | centralCommutes c => simpa only [unitaryLength_one] using hn
  | rowCommutes r i j => simpa only [unitaryLength_one] using hn
  | rowEquation r =>
    by_cases hb : S.rhs r = 1 <;> simp [hb, unitaryLength_rankOne, hn]

theorem rankOneAssignment_odd_error (r : R) (hr : S.rhs r = 1) :
    unitaryLength (rankOneAssignment d (FreeGroup.mk (relatorWord S (.rowEquation r)))) =
      2 / Real.sqrt d := by
  rw [rankOneAssignment_relator]
  simp only [hr, ite_true, unitaryLength_rankOne]

omit S in
theorem rankOneAssignment_J :
    rankOneAssignment (C := C) d (FreeGroup.of none) = rankOneUnitary d :=
  FreeGroup.lift_apply_of

end ThomGame.SolutionGroup

namespace ThomGame.Construction

open Analysis Filter
open scoped Topology

theorem sigma_rankOne_approximation (d : Nat) [NeZero d] :
    ∃ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
      IsApproxRepresentation (SolutionGroup.relators numberedSystem) (2 / Real.sqrt d) f ∧
      f (FreeGroup.of none) ≠ 1 ∧ unitaryLength (f (FreeGroup.of none)) = 2 / Real.sqrt d := by
  refine ⟨SolutionGroup.rankOneAssignment d,
    SolutionGroup.rankOneAssignment_isApprox numberedSystem d, ?_, ?_⟩
  · rw [SolutionGroup.rankOneAssignment_J]
    exact rankOneUnitary_ne_one d
  · rw [SolutionGroup.rankOneAssignment_J, unitaryLength_rankOne]

theorem rankOne_tolerance_tendsto :
    Tendsto (fun n : Nat => (2 : ℝ) / Real.sqrt (n + 1 : Nat)) atTop (𝓝 0) := by
  have ht := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hm := ht.const_mul (2 : ℝ)
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero,
    Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ)), Real.sqrt_one, mul_one_div,
    Nat.cast_add, Nat.cast_one] using hm

theorem sigma_no_positive_exact_tolerance (δ : ℝ) (hδ : 0 < δ) :
    ∃ (d : Nat), 0 < d ∧
      ∃ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
        IsApproxRepresentation (SolutionGroup.relators numberedSystem) δ f ∧
          f (FreeGroup.of none) ≠ 1 := by
  obtain ⟨n, hn⟩ := (rankOne_tolerance_tendsto.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨f, hf, hne, _⟩ := sigma_rankOne_approximation (n + 1)
  exact ⟨n + 1, Nat.succ_pos n, f, isApprox_mono hf hn.le, hne⟩

end ThomGame.Construction
