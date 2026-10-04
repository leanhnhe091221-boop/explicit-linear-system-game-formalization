module

public import ThomGame.Pictures.SunCancellation
public import ThomGame.Pictures.VertexSplitEuler
public import ThomGame.Pictures.EdgeContractionEuler

/-!
# The exact rotation surgery for opposite sun hubs

First contract the spoke, then cut off its two fixed ports, then split
the remaining four-port vertex into two degree-two joints. All operations
are actual transpositions of rotation targets on the original dart set.
The two removed spoke ports temporarily remain as isolated fixed ports.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv CycleSurgery FiniteReturn RibbonConnectivity RotationEuler
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

def cancelFirst : Fin 3 := if G.hubFlip s.left then 2 else 1
def cancelLast : Fin 3 := if G.hubFlip s.left then 1 else 2

noncomputable def cancelContractRotation : Perm G.Dart :=
  splice G.rotation (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3))

noncomputable def cancelLeftRotation : Perm G.Dart :=
  splice s.cancelContractRotation (.hub s.left (0 : Fin 3))
    (s.cancelContractRotation (.hub s.left (0 : Fin 3)))

noncomputable def cancelRimRotation : Perm G.Dart :=
  splice s.cancelLeftRotation (.hub s.right (0 : Fin 3))
    (s.cancelLeftRotation (.hub s.right (0 : Fin 3)))

noncomputable def cancelFullRotation : Perm G.Dart :=
  splice s.cancelRimRotation (.hub s.left s.cancelLast) (.hub s.right s.cancelFirst)

noncomputable def cancelFullPairing : Perm G.Dart :=
  splice G.pairing.perm (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3))

theorem cancelRim_last_left (hf : G.hubFlip s.left ≠ G.hubFlip s.right) :
    s.cancelRimRotation (.hub s.left s.cancelLast) = .hub s.right s.cancelLast := by
  cases hl : G.hubFlip s.left <;> cases hr : G.hubFlip s.right
  all_goals try exact (hf (hl.trans hr.symm)).elim
  all_goals simp [cancelRimRotation, cancelLeftRotation, cancelContractRotation, hl, hr,
    cancelLast, splice_apply, sun_rotation_hub, swap_apply_def, sun_hub_eq_iff,
    s.distinct, s.distinct.symm]
  all_goals decide +kernel

theorem cancelRim_last_right (hf : G.hubFlip s.left ≠ G.hubFlip s.right) :
    s.cancelRimRotation (.hub s.right s.cancelLast) = .hub s.right s.cancelFirst := by
  cases hl : G.hubFlip s.left <;> cases hr : G.hubFlip s.right
  all_goals try exact (hf (hl.trans hr.symm)).elim
  all_goals simp [cancelRimRotation, cancelLeftRotation, cancelContractRotation, hl, hr,
    cancelFirst, cancelLast, splice_apply, sun_rotation_hub, swap_apply_def, sun_hub_eq_iff,
    s.distinct, s.distinct.symm]
  all_goals decide +kernel

theorem cancelRim_sameCycle (hf : G.hubFlip s.left ≠ G.hubFlip s.right) :
    s.cancelRimRotation.SameCycle (.hub s.left s.cancelLast) (.hub s.right s.cancelFirst) := by
  have ha : s.cancelRimRotation.SameCycle (.hub s.left s.cancelLast)
      (s.cancelRimRotation (.hub s.left s.cancelLast)) := Perm.SameCycle.rfl.apply_right
  have hb : s.cancelRimRotation.SameCycle (.hub s.right s.cancelLast)
      (s.cancelRimRotation (.hub s.right s.cancelLast)) := Perm.SameCycle.rfl.apply_right
  rw [s.cancelRim_last_left hf] at ha
  rw [s.cancelRim_last_right hf] at hb
  exact ha.trans hb

theorem cancelFull_hub_left (hf : G.hubFlip s.left ≠ G.hubFlip s.right) (i : Fin 3) :
    s.cancelFullRotation (.hub s.left i) =
      if i = 0 then .hub s.left (0 : Fin 3) else .hub s.right i := by
  have hneg : (-1 : Fin 3) = 2 := by decide +kernel
  fin_cases i <;> cases hl : G.hubFlip s.left <;> cases hr : G.hubFlip s.right
  all_goals try exact (hf (hl.trans hr.symm)).elim
  all_goals simp [cancelFullRotation, cancelRimRotation, cancelLeftRotation,
    cancelContractRotation, cancelFirst, cancelLast, splice_apply, sun_rotation_hub,
    swap_apply_def, sun_hub_eq_iff, hl, hr, s.distinct, s.distinct.symm, hneg]

theorem cancelFull_hub_right (hf : G.hubFlip s.left ≠ G.hubFlip s.right) (i : Fin 3) :
    s.cancelFullRotation (.hub s.right i) =
      if i = 0 then .hub s.right (0 : Fin 3) else .hub s.left i := by
  have hneg : (-1 : Fin 3) = 2 := by decide +kernel
  fin_cases i <;> cases hl : G.hubFlip s.left <;> cases hr : G.hubFlip s.right
  all_goals try exact (hf (hl.trans hr.symm)).elim
  all_goals simp [cancelFullRotation, cancelRimRotation, cancelLeftRotation,
    cancelContractRotation, cancelFirst, cancelLast, splice_apply, sun_rotation_hub,
    swap_apply_def, sun_hub_eq_iff, hl, hr, s.distinct, s.distinct.symm, hneg]

theorem cancelFull_away {x : G.Dart}
    (hl : x.vertex ≠ .inr (.inl s.left)) (hr : x.vertex ≠ .inr (.inl s.right)) :
    s.cancelFullRotation x = G.rotation x := by
  have hrl (i : Fin 3) : G.rotation x ≠ .hub s.left i := by
    intro he
    exact hl ((G.vertex_rotation x).symm.trans (congrArg Port.vertex he))
  have hrr (i : Fin 3) : G.rotation x ≠ .hub s.right i := by
    intro he
    exact hr ((G.vertex_rotation x).symm.trans (congrArg Port.vertex he))
  cases hfl : G.hubFlip s.left <;> cases hfr : G.hubFlip s.right
  all_goals simp [cancelFullRotation, cancelRimRotation, cancelLeftRotation,
    cancelContractRotation, cancelFirst, cancelLast, splice_apply, sun_rotation_hub,
    swap_apply_def, sun_hub_eq_iff, hfl, hfr, s.distinct, s.distinct.symm, hrl, hrr]

theorem cancelFull_rotation (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (x : s.cancel.Dart) :
    s.cancelFullRotation (s.cancelPort x) = s.cancelPort (s.cancel.rotation x) := by
  cases x with
  | top i => exact s.cancelFull_away (by simp [cancelPort, Port.vertex]) (by simp [cancelPort, Port.vertex])
  | bottom i => exact s.cancelFull_away (by simp [cancelPort, Port.vertex]) (by simp [cancelPort, Port.vertex])
  | hub h i =>
    exact s.cancelFull_away
      (by simpa only [cancelPort, Port.vertex, ne_eq, Sum.inr.injEq, Sum.inl.injEq] using h.property.1)
      (by simpa only [cancelPort, Port.vertex, ne_eq, Sum.inr.injEq, Sum.inl.injEq] using h.property.2)
  | joint j side =>
    cases j with
    | inl j => exact s.cancelFull_away (by simp [cancelPort, Port.vertex]) (by simp [cancelPort, Port.vertex])
    | inr rim =>
      rw [s.cancel.rotation_joint]
      cases rim <;> cases side <;>
        simp [cancelPort, s.cancelFull_hub_left hf, s.cancelFull_hub_right hf]

theorem cancelFull_saturated (hf : G.hubFlip s.left ≠ G.hubFlip s.right)
    (hEuler : count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    count s.cancelFullRotation s.cancelFullPairing =
      2 * Nat.card (Component s.cancelFullRotation s.cancelFullPairing) := by
  have hn : ¬ G.rotation.SameCycle (.hub s.left (0 : Fin 3))
      (G.pairing.perm (.hub s.left (0 : Fin 3))) := by
    change ¬ G.rotation.SameCycle _ (G.pairing.twin _)
    rw [s.paired, G.rotation_sameCycle_iff]
    simpa only [Port.vertex, Sum.inr.injEq, Sum.inl.injEq] using s.distinct
  have hC := contractEdge_saturated G.rotation G.pairing.perm G.pairing.involutive hEuler _ hn
  have hi := removed_pair_involutive G.pairing.perm G.pairing.involutive
    (.hub s.left (0 : Fin 3))
  have hpair : G.pairing.perm (.hub s.left (0 : Fin 3)) = .hub s.right (0 : Fin 3) := s.paired
  simp only [hpair] at hC hi
  have hL := splitVertex_saturated s.cancelContractRotation s.cancelFullPairing hi hC
    (show s.cancelContractRotation.SameCycle (.hub s.left (0 : Fin 3))
      (s.cancelContractRotation (.hub s.left (0 : Fin 3))) from Perm.SameCycle.rfl.apply_right)
  have hR := splitVertex_saturated s.cancelLeftRotation s.cancelFullPairing hi hL
    (show s.cancelLeftRotation.SameCycle (.hub s.right (0 : Fin 3))
      (s.cancelLeftRotation (.hub s.right (0 : Fin 3))) from Perm.SameCycle.rfl.apply_right)
  exact splitVertex_saturated s.cancelRimRotation s.cancelFullPairing hi hR (s.cancelRim_sameCycle hf)

end ThomGame.Pictures.PortGraph.SunSpoke
