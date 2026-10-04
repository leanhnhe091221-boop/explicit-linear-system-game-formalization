module

public import ThomGame.Quantum.StateDependentRelations
public import ThomGame.Quantum.FiniteStrategy

/-! The state-dependent estimates apply to actual local finite-dimensional observables. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped TensorProduct

namespace ProjectiveMeasurement

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [CompleteSpace (H ⊗[ℂ] K)] [Fintype A]

theorem tensorLeft_observable (P : ProjectiveMeasurement H A) (s : A → ZMod 2) :
    (P.tensorLeft (K := K)).observable s = (P.observable s).rTensor K := by
  let L : (H →L[ℂ] H) →ₗ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) := {
    toFun := fun U => U.rTensor K
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  change (∑ a, bitSign (s a) • L (P.proj a)) = L (∑ a, bitSign (s a) • P.proj a)
  simp only [map_sum, map_smul]

theorem tensorRight_observable (P : ProjectiveMeasurement K A) (s : A → ZMod 2) :
    (P.tensorRight (H := H)).observable s = (P.observable s).lTensor H := by
  let L : (K →L[ℂ] K) →ₗ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) := {
    toFun := fun U => U.lTensor H
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  change (∑ a, bitSign (s a) • L (P.proj a)) = L (∑ a, bitSign (s a) • P.proj a)
  simp only [map_sum, map_smul]

end ProjectiveMeasurement

namespace FiniteStrategy

variable {R C : Type*} (T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2))

theorem toCommuting_state : T.toCommuting.state = T.state := rfl

noncomputable def localAliceBit (r : R) (i : Fin 3) : LocalSpace T.dimAlice →L[ℂ] LocalSpace T.dimAlice :=
  (T.alice r).observable (fun a => a i)

noncomputable def localBobBit (c : C) : LocalSpace T.dimBob →L[ℂ] LocalSpace T.dimBob :=
  (T.bob c).observable id

theorem localAliceBit_selfAdjoint (r : R) (i : Fin 3) : IsSelfAdjoint (T.localAliceBit r i) :=
  (T.alice r).observable_selfAdjoint _

theorem localBobBit_selfAdjoint (c : C) : IsSelfAdjoint (T.localBobBit c) :=
  (T.bob c).observable_selfAdjoint _

theorem localAliceBit_square (r : R) (i : Fin 3) : T.localAliceBit r i * T.localAliceBit r i = 1 :=
  (T.alice r).observable_square _

theorem localBobBit_square (c : C) : T.localBobBit c * T.localBobBit c = 1 :=
  (T.bob c).observable_square _

theorem localAliceBit_commute (r : R) (i j : Fin 3) :
    Commute (T.localAliceBit r i) (T.localAliceBit r j) := (T.alice r).observable_commute _ _

theorem toCommuting_aliceBit (r : R) (i : Fin 3) :
    T.toCommuting.aliceBit r i = (T.localAliceBit r i).rTensor (LocalSpace T.dimBob) :=
  (T.alice r).tensorLeft_observable _

theorem toCommuting_bobBit (c : C) :
    T.toCommuting.bobBit c = (T.localBobBit c).lTensor (LocalSpace T.dimAlice) :=
  (T.bob c).tensorRight_observable _

variable [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] (S : SparseSystem R C)

theorem near_perfect_local_consistency {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (r : R) (i : Fin 3) :
    ‖(T.localAliceBit r i).rTensor (LocalSpace T.dimBob) T.state -
      (T.localBobBit (S.column r i)).lTensor (LocalSpace T.dimAlice) T.state‖ ≤
        2 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  simpa only [T.toCommuting_aliceBit, T.toCommuting_bobBit, T.toCommuting_state] using
    (T.toCommuting.near_perfect_state_relations S h).1 r i

theorem near_perfect_local_row {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (r : R) :
    ‖(T.localBobBit (S.column r 0) * T.localBobBit (S.column r 1) *
      T.localBobBit (S.column r 2)).lTensor (LocalSpace T.dimAlice) T.state -
        bitSign (S.rhs r) • T.state‖ ≤ 8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  simpa only [T.toCommuting_bobBit, ← ContinuousLinearMap.lTensor_mul, T.toCommuting_state] using
    (T.toCommuting.near_perfect_state_relations S h).2.1 r

theorem near_perfect_local_commutator {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (r : R) (i j : Fin 3) :
    ‖(T.localBobBit (S.column r i) * T.localBobBit (S.column r j) -
      T.localBobBit (S.column r j) * T.localBobBit (S.column r i)).lTensor
        (LocalSpace T.dimAlice) T.state‖ ≤ 8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  simpa only [T.toCommuting_bobBit, ← ContinuousLinearMap.lTensor_mul,
    ← ContinuousLinearMap.lTensor_sub, ← sub_apply, T.toCommuting_state] using
    (T.toCommuting.near_perfect_state_relations S h).2.2 r i j

end FiniteStrategy
end ThomGame.Quantum
