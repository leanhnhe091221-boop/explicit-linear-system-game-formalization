module

public import ThomGame.Quantum.ProjectiveMeasurement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module

/-! The two spectral projections of a self-adjoint involution, labelled by bits. -/

@[expose] public section
namespace ThomGame.Quantum

def bitSign (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

theorem bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have ha := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 by omega) with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    change a.val = 1
    exact h

theorem bitSign_zero : bitSign 0 = 1 := by norm_num [bitSign]
theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [h11, zero_add, add_zero, bitSign_zero, bitSign_one] <;> norm_num

theorem bitSign_sq (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  rcases bit_cases a with rfl | rfl <;> norm_num [bitSign]

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    first | rfl | norm_num [bitSign] at h

theorem bitSign_selfAdjoint (a : ZMod 2) : IsSelfAdjoint (bitSign a) := by
  rcases bit_cases a with rfl | rfl <;> norm_num [bitSign, IsSelfAdjoint]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def bitProjection (U : H →L[ℂ] H) (a : ZMod 2) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (1 + bitSign a • U)

theorem bitProjection_selfAdjoint (U : H →L[ℂ] H) (hU : IsSelfAdjoint U) (a : ZMod 2) :
    IsSelfAdjoint (bitProjection U a) :=
  (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [IsSelfAdjoint]).smul
    ((IsSelfAdjoint.one (H →L[ℂ] H)).add ((bitSign_selfAdjoint a).smul hU))

omit [CompleteSpace H] in
theorem bitProjection_idempotent (U : H →L[ℂ] H) (hU : U * U = 1) (a : ZMod 2) :
    bitProjection U a * bitProjection U a = bitProjection U a := by
  rcases bit_cases a with rfl | rfl <;>
    norm_num [bitProjection, bitSign, smul_mul_assoc, mul_smul_comm, mul_add, add_mul,
      one_mul, mul_one, hU, smul_smul] <;> module

omit [CompleteSpace H] in
theorem bitProjection_orthogonal (U : H →L[ℂ] H) (hU : U * U = 1)
    (a b : ZMod 2) (hab : a ≠ b) : bitProjection U a * bitProjection U b = 0 := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> try contradiction
  all_goals
    norm_num [bitProjection, bitSign, smul_mul_assoc, mul_smul_comm, mul_add, add_mul,
      one_mul, mul_one, hU, smul_smul] <;> module

omit [CompleteSpace H] in
theorem bitProjection_sum (U : H →L[ℂ] H) : ∑ a : ZMod 2, bitProjection U a = 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  norm_num [bitProjection, bitSign]
  module

omit [CompleteSpace H] in
theorem bitProjection_eigen (U : H →L[ℂ] H) (hU : U * U = 1) (a : ZMod 2) :
    U * bitProjection U a = bitSign a • bitProjection U a := by
  rcases bit_cases a with rfl | rfl <;>
    norm_num [bitProjection, bitSign, mul_smul_comm, mul_add, mul_one, hU, smul_smul] <;> module

omit [CompleteSpace H] in
theorem bitProjection_commute (U V : H →L[ℂ] H) (h : Commute U V) (a : ZMod 2) :
    Commute (bitProjection U a) V := by
  change bitProjection U a * V = V * bitProjection U a
  simp [bitProjection, add_mul, mul_add, h.eq]

omit [CompleteSpace H] in
theorem bitProjections_commute (U V : H →L[ℂ] H) (h : Commute U V) (a b : ZMod 2) :
    Commute (bitProjection U a) (bitProjection V b) :=
  (bitProjection_commute V _ (bitProjection_commute U V h a).symm b).symm

noncomputable def binaryMeasurement (U : H →L[ℂ] H) (hs : IsSelfAdjoint U) (hq : U * U = 1) :
    ProjectiveMeasurement H (ZMod 2) where
  proj := bitProjection U
  selfAdjoint := bitProjection_selfAdjoint U hs
  idempotent := bitProjection_idempotent U hq
  orthogonal := bitProjection_orthogonal U hq
  complete := bitProjection_sum U

end ThomGame.Quantum
