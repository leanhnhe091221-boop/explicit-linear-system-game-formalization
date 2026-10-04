module

public import ThomGame.Quantum.TripleMeasurement
public import ThomGame.Quantum.IncidenceGame

/-! From actual involutive observables and a state to perfect linear-system play. -/

@[expose] public section
namespace ThomGame.Quantum

variable {R C : Type*} (S : SparseSystem R C) (H : Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure LinearSystemObservables where
  state : H
  norm_state : ‖state‖ = 1
  left : C → H →L[ℂ] H
  right : C → H →L[ℂ] H
  left_selfAdjoint : ∀ c, IsSelfAdjoint (left c)
  right_selfAdjoint : ∀ c, IsSelfAdjoint (right c)
  left_square : ∀ c, left c * left c = 1
  right_square : ∀ c, right c * right c = 1
  cross : ∀ c d, Commute (left c) (right d)
  row_commute : ∀ r i j, Commute (left (S.column r i)) (left (S.column r j))
  row_state : ∀ r, (left (S.column r 0) * left (S.column r 1) * left (S.column r 2)) state =
    bitSign (S.rhs r) • state
  consistent_state : ∀ c, left c state = right c state

namespace LinearSystemObservables

variable {S H} (O : LinearSystemObservables S H)

noncomputable def alice (r : R) : ProjectiveMeasurement H (Fin 3 → ZMod 2) :=
  tripleMeasurement (fun i => O.left (S.column r i))
    (fun i => O.left_selfAdjoint (S.column r i)) (fun i => O.left_square (S.column r i)) (O.row_commute r)

noncomputable def bob (c : C) : ProjectiveMeasurement H (ZMod 2) :=
  binaryMeasurement (O.right c) (O.right_selfAdjoint c) (O.right_square c)

theorem alice_commute_left (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) :
    Commute ((O.alice r).proj a) (O.left (S.column r i)) :=
  tripleMeasurement_commute _ _ _ _ a _ (fun j => O.row_commute r j i)

theorem alice_commute_right (r : R) (a : Fin 3 → ZMod 2) (c : C) :
    Commute ((O.alice r).proj a) (O.right c) :=
  tripleMeasurement_commute _ _ _ _ a _ (fun i => O.cross (S.column r i) c)

theorem alice_eigen (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) :
    O.left (S.column r i) * (O.alice r).proj a = bitSign (a i) • (O.alice r).proj a :=
  tripleMeasurement_eigen (fun j => O.left (S.column r j))
    (fun j => O.left_selfAdjoint (S.column r j)) (fun j => O.left_square (S.column r j))
    (O.row_commute r) a i

theorem alice_product_eigen (r : R) (a : Fin 3 → ZMod 2) :
    (O.left (S.column r 0) * O.left (S.column r 1) * O.left (S.column r 2)) * (O.alice r).proj a =
      bitSign (∑ i, a i) • (O.alice r).proj a :=
  tripleMeasurement_product_eigen (fun j => O.left (S.column r j))
    (fun j => O.left_selfAdjoint (S.column r j)) (fun j => O.left_square (S.column r j))
    (O.row_commute r) a

theorem alice_bob_commute (r : R) (c : C) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    Commute ((O.alice r).proj a) ((O.bob c).proj b) :=
  (bitProjection_commute (O.right c) _ (O.alice_commute_right r a c).symm b).symm

noncomputable def strategy : CommutingStrategy R C (Fin 3 → ZMod 2) (ZMod 2) H where
  state := O.state
  norm_state := O.norm_state
  alice := O.alice
  bob := O.bob
  commute := O.alice_bob_commute

noncomputable def outcome (r : R) (a : Fin 3 → ZMod 2) (c : C) (b : ZMod 2) : H →L[ℂ] H :=
  (O.alice r).proj a * (O.bob c).proj b

theorem outcome_commute_left (r : R) (a : Fin 3 → ZMod 2) (c : C) (b : ZMod 2) (i : Fin 3) :
    Commute (O.outcome r a c b) (O.left (S.column r i)) :=
  (O.alice_commute_left r i a).mul_left
    (bitProjection_commute (O.right c) _ (O.cross (S.column r i) c).symm b)

theorem outcome_commute_right (r : R) (a : Fin 3 → ZMod 2) (c : C) (b : ZMod 2) :
    Commute (O.outcome r a c b) (O.right c) :=
  (O.alice_commute_right r a c).mul_left
    (bitProjection_commute (O.right c) _ (Commute.refl _) b)

theorem outcome_eigen_left (r : R) (a : Fin 3 → ZMod 2) (c : C) (b : ZMod 2) (i : Fin 3) :
    O.left (S.column r i) * O.outcome r a c b = bitSign (a i) • O.outcome r a c b := by
  rw [outcome, ← mul_assoc, O.alice_eigen]
  simp only [smul_mul_assoc]

theorem outcome_eigen_right (r : R) (a : Fin 3 → ZMod 2) (c : C) (b : ZMod 2) :
    O.right c * O.outcome r a c b = bitSign b • O.outcome r a c b := by
  change O.right c * ((O.alice r).proj a * bitProjection (O.right c) b) = _
  rw [← mul_assoc, ← (O.alice_commute_right r a c).eq, mul_assoc,
    bitProjection_eigen (O.right c) (O.right_square c)]
  simp only [mul_smul_comm]
  rfl

omit [CompleteSpace H] in
theorem zero_of_distinct_bits (a b : ZMod 2) (hab : a ≠ b) (v : H)
    (h : bitSign a • v = bitSign b • v) : v = 0 := by
  have hz : (bitSign a - bitSign b) • v = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (bitSign_injective.ne hab))

theorem outcome_zero_of_inconsistent (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2)
    (h : a i ≠ b) : O.outcome r a (S.column r i) b O.state = 0 := by
  let M := O.outcome r a (S.column r i) b
  have hl := DFunLike.congr_fun (O.outcome_eigen_left r a (S.column r i) b i) O.state
  have hr := DFunLike.congr_fun (O.outcome_eigen_right r a (S.column r i) b) O.state
  have he : O.left (S.column r i) (M O.state) = O.right (S.column r i) (M O.state) := by
    calc
      O.left (S.column r i) (M O.state) = M (O.left (S.column r i) O.state) :=
        (DFunLike.congr_fun (O.outcome_commute_left r a (S.column r i) b i).eq O.state).symm
      _ = M (O.right (S.column r i) O.state) := by rw [O.consistent_state]
      _ = O.right (S.column r i) (M O.state) :=
        DFunLike.congr_fun (O.outcome_commute_right r a (S.column r i) b).eq O.state
  exact zero_of_distinct_bits (a i) b h (M O.state) (hl.symm.trans (he.trans hr))

theorem outcome_zero_of_wrong_parity (r : R) (a : Fin 3 → ZMod 2) (c : C) (b : ZMod 2)
    (h : (∑ i, a i) ≠ S.rhs r) : O.outcome r a c b O.state = 0 := by
  let M := O.outcome r a c b
  let K := O.left (S.column r 0) * O.left (S.column r 1) * O.left (S.column r 2)
  have he : K * M = bitSign (∑ i, a i) • M := by
    change K * ((O.alice r).proj a * (O.bob c).proj b) = _
    rw [← mul_assoc, O.alice_product_eigen, smul_mul_assoc]
    rfl
  have hc : Commute M K :=
    ((O.outcome_commute_left r a c b 0).mul_right
      (O.outcome_commute_left r a c b 1)).mul_right (O.outcome_commute_left r a c b 2)
  have hv : bitSign (∑ i, a i) • M O.state = bitSign (S.rhs r) • M O.state := by
    calc
      bitSign (∑ i, a i) • M O.state = K (M O.state) :=
        (DFunLike.congr_fun he O.state).symm
      _ = M (K O.state) := (DFunLike.congr_fun hc.eq O.state).symm
      _ = bitSign (S.rhs r) • M O.state := by rw [show K O.state = _ from O.row_state r, map_smul]
  exact zero_of_distinct_bits _ _ h _ hv

theorem rejected_probability_zero (r : R) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2)
    (h : ¬ S.Accepts r i a b) : O.strategy.correlation r (S.column r i) a b = 0 := by
  have hv : O.outcome r a (S.column r i) b O.state = 0 := by
    by_cases hp : (∑ j, a j) = S.rhs r
    · exact O.outcome_zero_of_inconsistent r i a b (fun hb => h ⟨hp, hb⟩)
    · exact O.outcome_zero_of_wrong_parity r a (S.column r i) b hp
  change ‖O.outcome r a (S.column r i) b O.state‖ ^ 2 = 0
  rw [hv, norm_zero, zero_pow (by decide)]

theorem perfect_success [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] :
    S.incidenceGame.success O.strategy.correlation = 1 :=
  S.incidenceGame_perfect_of_zero_rejected _ O.strategy.isProbabilityTable O.rejected_probability_zero

end LinearSystemObservables
end ThomGame.Quantum
