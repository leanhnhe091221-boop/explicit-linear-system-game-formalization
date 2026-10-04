module

public import ThomGame.Pictures.CircuitRegionCapping
public import ThomGame.Pictures.FullSeamState
public import ThomGame.Pictures.VertexJoinEuler

/-!
# Gluing oppositely oriented capped boundaries

The lower cap turns forward and the upper cap turns backward. Gluing
their numbered leaves exchanges shifted targets in the disjoint capped
maps. The first exchange joins different components; each later exchange
splits one rotation orbit. This proves Euler saturation of the actual
composition, including disconnected inputs and the empty interface.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv CycleSurgery RibbonConnectivity RotationEuler
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P [] w) (H : PortGraph P w [])

/-- Advance the lower boundary targets by one slot. -/
noncomputable def capSeamFrame : Perm (G.Dart ⊕ H.Dart) where
  toFun
    | .inl (.bottom i) => .inl (.bottom (finRotate _ i))
    | a => a
  invFun
    | .inl (.bottom i) => .inl (.bottom ((finRotate _).symm i))
    | a => a
  left_inv a := by rcases a with a | a <;> cases a <;> simp only [Equiv.symm_apply_apply]
  right_inv a := by rcases a with a | a <;> cases a <;> simp only [Equiv.apply_symm_apply]

/-- The actual intermediate rotation after the first `k` shifted exchanges. -/
noncomputable def capSeamRotation (k : Nat) : Perm (G.Dart ⊕ H.Dart) :=
  capSeamFrame G H * partialDartSwap G H k * (capSeamFrame G H)⁻¹ *
    Equiv.sumCongr G.cappedRotation H.cappedRotation

theorem capSeamRotation_zero :
    capSeamRotation G H 0 = Equiv.sumCongr G.cappedRotation H.cappedRotation := by
  simp [capSeamRotation, partialDartSwap_zero]

theorem capSeamRotation_step (i : Fin w.length) :
    capSeamRotation G H (i.val + 1) =
      splice (capSeamRotation G H i.val) (.inl (.bottom (finRotate _ i))) (.inr (.top i)) := by
  unfold capSeamRotation
  rw [partialDartSwap_step, ← mul_assoc (capSeamFrame G H), mul_swap_eq_swap_mul]
  rfl

theorem capSeamRotation_bottom (k : Nat) (i : Fin w.length) :
    capSeamRotation G H k (.inl (.bottom i)) =
      if i.val < k then .inr (.top i) else .inl (.bottom (finRotate _ i)) := by
  simp only [capSeamRotation, Perm.mul_apply, sumCongr_apply, Sum.map_inl,
    G.cappedRotation_bottom]
  change capSeamFrame G H (partialDartSwap G H k
    (.inl (.bottom ((finRotate _).symm (finRotate _ i))))) = _
  rw [Equiv.symm_apply_apply]
  by_cases hi : i.val < k <;> simp [partialDartSwap, hi, capSeamFrame]

theorem capSeamRotation_top (k : Nat) (i : Fin w.length) :
    capSeamRotation G H k (.inr (.top i)) =
      if ((finRotate _).symm i).val < k then .inl (.bottom i)
      else .inr (.top ((finRotate _).symm i)) := by
  simp only [capSeamRotation, Perm.mul_apply, sumCongr_apply, Sum.map_inr,
    H.cappedRotation_top]
  change capSeamFrame G H (partialDartSwap G H k
    (.inr (.top ((finRotate _).symm i)))) = _
  by_cases hi : ((finRotate _).symm i).val < k <;>
    simp only [partialDartSwap, Equiv.coe_fn_mk, hi, ite_true, ite_false,
      capSeamFrame, Equiv.apply_symm_apply]

theorem capSeamRotation_sameCycle (i : Fin w.length) (hi : 0 < i.val) :
    (capSeamRotation G H i.val).SameCycle
      (.inl (.bottom (finRotate _ i))) (.inr (.top i)) := by
  have hp : ((finRotate _).symm i).val < i.val := by
    let : NeZero w.length := ⟨by omega⟩
    exact (finRotate_symm_lt_iff_ne_zero i).mpr (fun h => by simp [h] at hi)
  have h₁ : capSeamRotation G H i.val (.inr (.top i)) = .inl (.bottom i) := by
    rw [capSeamRotation_top, ite_eq_left hp]
  have h₂ : capSeamRotation G H i.val (.inl (.bottom i)) =
      .inl (.bottom (finRotate _ i)) := by
    rw [capSeamRotation_bottom, ite_eq_right (Nat.lt_irrefl _)]
  have hs : (capSeamRotation G H i.val).SameCycle (.inr (.top i))
      (capSeamRotation G H i.val (capSeamRotation G H i.val (.inr (.top i)))) :=
    Perm.SameCycle.rfl.apply_right.apply_right
  rw [h₁, h₂] at hs
  exact hs.symm

theorem capSeamRotation_saturated
    (hG : count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm))
    (hH : count H.cappedRotation H.pairing.perm =
      2 * Nat.card (Component H.cappedRotation H.pairing.perm))
    (k : Nat) (hk : k ≤ w.length) :
    count (capSeamRotation G H k) (Equiv.sumCongr G.pairing.perm H.pairing.perm) =
      2 * Nat.card (Component (capSeamRotation G H k)
        (Equiv.sumCongr G.pairing.perm H.pairing.perm)) := by
  induction k with
  | zero =>
    rw [capSeamRotation_zero, count_sum, component_card_sum, hG, hH]
    push_cast
    omega
  | succ k ih =>
    let i : Fin w.length := ⟨k, by omega⟩
    have hs := ih (by omega)
    rw [show k + 1 = i.val + 1 from rfl, capSeamRotation_step]
    by_cases hz : k = 0
    · subst k
      rw [capSeamRotation_zero] at hs ⊢
      apply joinVertex_saturated _ _ hs
      exact not_connected_sum G.cappedRotation G.pairing.perm H.cappedRotation H.pairing.perm _ _
    · apply splitVertex_saturated _ _ _ hs
        (capSeamRotation_sameCycle G H i (show 0 < k by omega))
      rintro (a | a)
      · exact congrArg Sum.inl (G.pairing.involutive a)
      · exact congrArg Sum.inr (H.pairing.involutive a)

theorem capSeamRotation_all (a : G.Dart ⊕ H.Dart) :
    capSeamRotation G H w.length a =
      seamSwap G H (Equiv.sumCongr G.rotation H.rotation a) := by
  rcases a with a | a
  · cases a with
    | top i => exact i.elim0
    | bottom i => rw [capSeamRotation_bottom, ite_eq_left i.isLt]; rfl
    | hub h i =>
      have hc : G.cappedRotation (.hub h i) = G.rotation (.hub h i) :=
        G.cappingTargets_unmarked (.hub h (G.hubRotation h i)) id
      simp only [capSeamRotation, Perm.mul_apply, sumCongr_apply, Sum.map_inl, hc]
      rfl
    | joint j b =>
      have hc : G.cappedRotation (.joint j b) = G.rotation (.joint j b) :=
        G.cappingTargets_unmarked (.joint j (!b)) id
      simp only [capSeamRotation, Perm.mul_apply, sumCongr_apply, Sum.map_inl, hc]
      rfl
  · cases a with
    | top i => rw [capSeamRotation_top, ite_eq_left ((finRotate _).symm i).isLt]; rfl
    | bottom i => exact i.elim0
    | hub h i =>
      simp only [capSeamRotation, Perm.mul_apply, sumCongr_apply, Sum.map_inr, H.cappedRotation_hub]
      rfl
    | joint j b =>
      have hc : H.cappedRotation (.joint j b) = H.rotation (.joint j b) :=
        H.cappingTargets_unmarked (.joint j (!b)) id
      simp only [capSeamRotation, Perm.mul_apply, sumCongr_apply, Sum.map_inr, hc]
      rfl

theorem comp_saturated_of_capped
    (hG : count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm))
    (hH : count H.cappedRotation H.pairing.perm =
      2 * Nat.card (Component H.cappedRotation H.pairing.perm)) :
    count (G.comp H).rotation (G.comp H).pairing.perm =
      2 * Nat.card (Component (G.comp H).rotation (G.comp H).pairing.perm) := by
  have hr (a : G.Dart ⊕ H.Dart) :
      (G.comp H).rotation (compPorts G H a) =
        compPorts G H (capSeamRotation G H w.length a) := by
    rw [capSeamRotation_all, rotation_compPorts]
  have ht (a : G.Dart ⊕ H.Dart) :
      (G.comp H).pairing.perm (compPorts G H a) =
        compPorts G H (Equiv.sumCongr G.pairing.perm H.pairing.perm a) :=
    twin_compPorts G H a
  have he := capSeamRotation_saturated G H hG hH w.length le_rfl
  rwa [count_congr _ _ _ _ (compPorts G H) hr ht,
    Nat.card_congr (componentCongrEquiv _ _ _ _ (compPorts G H) hr ht)] at he

end ThomGame.Pictures.PortGraph
