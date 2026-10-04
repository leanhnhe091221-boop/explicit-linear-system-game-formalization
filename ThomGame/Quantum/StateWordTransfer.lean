module

public import ThomGame.Quantum.StrategyObservables

/-! Transfer short words between commuting isometric actions on the same state. -/

@[expose] public section
namespace ThomGame.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem pair_state_transfer (A B C D : H →L[ℂ] H)
    (hB : ∀ ξ, ‖B ξ‖ = ‖ξ‖) (hC : ∀ ξ, ‖C ξ‖ = ‖ξ‖) (hc : Commute B C) (ψ : H) :
    ‖(B * D) ψ - (C * A) ψ‖ ≤ ‖D ψ - C ψ‖ + ‖B ψ - A ψ‖ := by
  have he : (B * D) ψ - (C * A) ψ = B (D ψ - C ψ) + C (B ψ - A ψ) := by
    have h := DFunLike.congr_fun hc.eq ψ
    simp only [mul_apply_eq_comp] at h ⊢
    rw [map_sub, map_sub, h]
    module
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [hB, hC])

theorem triple_state_transfer (A B : Fin 3 → H →L[ℂ] H)
    (hA : ∀ i ξ, ‖A i ξ‖ = ‖ξ‖) (hB : ∀ i ξ, ‖B i ξ‖ = ‖ξ‖)
    (hc : ∀ i j, Commute (A i) (B j)) (ψ : H) :
    ‖(B 0 * B 1 * B 2) ψ - (A 2 * A 1 * A 0) ψ‖ ≤
      ‖B 2 ψ - A 2 ψ‖ + ‖B 1 ψ - A 1 ψ‖ + ‖B 0 ψ - A 0 ψ‖ := by
  have h := pair_state_transfer (A 0) (B 0) (A 2 * A 1) (B 1 * B 2)
    (hB 0) (fun ξ => by simp only [mul_apply_eq_comp, hA])
    (((hc 2 0).symm).mul_right (hc 1 0).symm) ψ
  rw [← mul_assoc] at h
  exact h.trans (add_le_add
    (pair_state_transfer (A 1) (B 1) (A 2) (B 2) (hB 1) (hA 2) (hc 2 1).symm ψ) le_rfl)

namespace CommutingStrategy

variable {R C : Type*} [CompleteSpace H]
  (T : CommutingStrategy R C (Fin 3 → ZMod 2) (ZMod 2) H) (S : SparseSystem R C)

theorem bob_pair_state_transfer (r : R) (i j : Fin 3) :
    ‖(T.bobBit (S.column r i) * T.bobBit (S.column r j)) T.state -
      (T.aliceBit r i * T.aliceBit r j) T.state‖ ≤
      ‖T.aliceBit r j T.state - T.bobBit (S.column r j) T.state‖ +
      ‖T.aliceBit r i T.state - T.bobBit (S.column r i) T.state‖ := by
  have h := pair_state_transfer (T.aliceBit r i) (T.bobBit (S.column r i))
    (T.aliceBit r j) (T.bobBit (S.column r j)) (T.bobBit_norm _) (T.aliceBit_norm r j)
    (T.bit_cross_commute r j _).symm T.state
  rw [(T.aliceBit_commute r j i).eq, norm_sub_rev (T.bobBit _ T.state),
    norm_sub_rev (T.bobBit _ T.state)] at h
  exact h

theorem bob_triple_state_transfer (r : R) :
    ‖(T.bobBit (S.column r 0) * T.bobBit (S.column r 1) * T.bobBit (S.column r 2)) T.state -
      (T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2) T.state‖ ≤
      ‖T.aliceBit r 2 T.state - T.bobBit (S.column r 2) T.state‖ +
      ‖T.aliceBit r 1 T.state - T.bobBit (S.column r 1) T.state‖ +
      ‖T.aliceBit r 0 T.state - T.bobBit (S.column r 0) T.state‖ := by
  have h := triple_state_transfer (T.aliceBit r) (fun i => T.bobBit (S.column r i))
    (T.aliceBit_norm r) (fun i => T.bobBit_norm (S.column r i))
    (fun i j => T.bit_cross_commute r i (S.column r j)) T.state
  have he : T.aliceBit r 2 * T.aliceBit r 1 * T.aliceBit r 0 =
      T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2 := by
    rw [(T.aliceBit_commute r 2 1).eq, mul_assoc, (T.aliceBit_commute r 2 0).eq,
      ← mul_assoc, (T.aliceBit_commute r 1 0).eq]
  rw [he] at h
  simpa only [norm_sub_rev] using h

end CommutingStrategy
end ThomGame.Quantum
