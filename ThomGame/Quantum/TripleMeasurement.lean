module

public import ThomGame.Quantum.BinaryMeasurement
public import ThomGame.Quantum.JointMeasurement

/-! The actual joint measurement of a commuting row of three involutions. -/

@[expose] public section
namespace ThomGame.Quantum

def tripleOutcomeEquiv : (Fin 3 → ZMod 2) ≃ ((ZMod 2 × ZMod 2) × ZMod 2) where
  toFun a := ((a 0, a 1), a 2)
  invFun a := ![a.1.1, a.1.2, a.2]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by rcases a with ⟨⟨a, b⟩, c⟩; rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def tripleMeasurement (U : Fin 3 → H →L[ℂ] H)
    (hs : ∀ i, IsSelfAdjoint (U i)) (hq : ∀ i, U i * U i = 1)
    (hc : ∀ i j, Commute (U i) (U j)) : ProjectiveMeasurement H (Fin 3 → ZMod 2) :=
  (((binaryMeasurement (U 0) (hs 0) (hq 0)).joint
    (binaryMeasurement (U 1) (hs 1) (hq 1))
    (fun a b => bitProjections_commute (U 0) (U 1) (hc 0 1) a b)).joint
      (binaryMeasurement (U 2) (hs 2) (hq 2)) (fun a b =>
        (bitProjections_commute (U 0) (U 2) (hc 0 2) a.1 b).mul_left
          (bitProjections_commute (U 1) (U 2) (hc 1 2) a.2 b))).relabel tripleOutcomeEquiv

theorem tripleMeasurement_proj (U : Fin 3 → H →L[ℂ] H)
    (hs : ∀ i, IsSelfAdjoint (U i)) (hq : ∀ i, U i * U i = 1)
    (hc : ∀ i j, Commute (U i) (U j)) (a : Fin 3 → ZMod 2) :
    (tripleMeasurement U hs hq hc).proj a =
      bitProjection (U 0) (a 0) * bitProjection (U 1) (a 1) * bitProjection (U 2) (a 2) := rfl

theorem tripleMeasurement_commute (U : Fin 3 → H →L[ℂ] H)
    (hs : ∀ i, IsSelfAdjoint (U i)) (hq : ∀ i, U i * U i = 1)
    (hc : ∀ i j, Commute (U i) (U j)) (a : Fin 3 → ZMod 2)
    (V : H →L[ℂ] H) (hV : ∀ i, Commute (U i) V) :
    Commute ((tripleMeasurement U hs hq hc).proj a) V :=
  ((bitProjection_commute (U 0) V (hV 0) (a 0)).mul_left
    (bitProjection_commute (U 1) V (hV 1) (a 1))).mul_left
      (bitProjection_commute (U 2) V (hV 2) (a 2))

theorem tripleMeasurement_eigen (U : Fin 3 → H →L[ℂ] H)
    (hs : ∀ i, IsSelfAdjoint (U i)) (hq : ∀ i, U i * U i = 1)
    (hc : ∀ i j, Commute (U i) (U j)) (a : Fin 3 → ZMod 2) (i : Fin 3) :
    U i * (tripleMeasurement U hs hq hc).proj a =
      bitSign (a i) • (tripleMeasurement U hs hq hc).proj a := by
  let P := fun j => bitProjection (U j) (a j)
  have h0 : U 0 * (P 0 * P 1 * P 2) = bitSign (a 0) • (P 0 * P 1 * P 2) := by
    rw [← mul_assoc, ← mul_assoc, bitProjection_eigen (U 0) (hq 0)]
    simp only [P, smul_mul_assoc]
  have h1 : U 1 * (P 0 * P 1 * P 2) = bitSign (a 1) • (P 0 * P 1 * P 2) := by
    calc
      U 1 * (P 0 * P 1 * P 2) = (P 0 * U 1) * P 1 * P 2 := by
        rw [← mul_assoc, ← mul_assoc, (bitProjection_commute (U 0) (U 1) (hc 0 1) (a 0)).eq]
      _ = P 0 * (U 1 * P 1) * P 2 := by simp only [mul_assoc]
      _ = bitSign (a 1) • (P 0 * P 1 * P 2) := by
        rw [bitProjection_eigen (U 1) (hq 1)]
        simp only [P, mul_smul_comm, smul_mul_assoc]
  have h2 : U 2 * (P 0 * P 1 * P 2) = bitSign (a 2) • (P 0 * P 1 * P 2) := by
    have hcomm : Commute (P 0 * P 1) (U 2) :=
      (bitProjection_commute (U 0) (U 2) (hc 0 2) (a 0)).mul_left
        (bitProjection_commute (U 1) (U 2) (hc 1 2) (a 1))
    calc
      U 2 * (P 0 * P 1 * P 2) = (P 0 * P 1) * (U 2 * P 2) := by
        rw [← mul_assoc, ← hcomm.eq, mul_assoc]
      _ = bitSign (a 2) • (P 0 * P 1 * P 2) := by
        rw [bitProjection_eigen (U 2) (hq 2)]
        simp only [P, mul_smul_comm]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem tripleMeasurement_product_eigen (U : Fin 3 → H →L[ℂ] H)
    (hs : ∀ i, IsSelfAdjoint (U i)) (hq : ∀ i, U i * U i = 1)
    (hc : ∀ i j, Commute (U i) (U j)) (a : Fin 3 → ZMod 2) :
    (U 0 * U 1 * U 2) * (tripleMeasurement U hs hq hc).proj a =
      bitSign (∑ i, a i) • (tripleMeasurement U hs hq hc).proj a := by
  have ha : (∑ i, a i) = a 0 + a 1 + a 2 := by simp [Fin.sum_univ_succ, add_assoc]
  rw [ha, bitSign_add, bitSign_add]
  simp only [mul_assoc, tripleMeasurement_eigen U hs hq hc a, mul_smul_comm, smul_smul]
  module

end ThomGame.Quantum
