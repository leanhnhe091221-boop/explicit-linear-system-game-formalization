module

public import ThomGame.Pictures.SunSwitch
public import ThomGame.Pictures.GraphSmoothing

/-!
# Cancelling the two hubs of an internal sun spoke

Remove the spoke and its two equally labelled hubs, replacing their rim
ports by two equally labelled degree-two joints. The exact surviving
pairing is transported along an explicit port equivalence. This graph
construction needs no orientation hypothesis; its Euler preservation
requires opposite hub orientations and is proved separately.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

abbrev CancelHub := {h : G.Hub // h ≠ s.left ∧ h ≠ s.right}
abbrev CancelDart := Port (sunPresentation n b) u v s.CancelHub (G.Joint ⊕ Bool)
  (fun h => G.hubLabel h.val)

def cancelPort : s.CancelDart → G.Dart
  | .top i => .top i
  | .bottom i => .bottom i
  | .hub h i => .hub h.val i
  | .joint (.inl j) side => .joint j side
  | .joint (.inr rim) side => .hub (if side then s.right else s.left)
      (if rim then (2 : Fin 3) else (1 : Fin 3))

theorem cancelPort_kept (x : s.CancelDart) : s.Kept (s.cancelPort x) := by
  cases x with
  | top i => simp [cancelPort, Kept]
  | bottom i => simp [cancelPort, Kept]
  | hub h i =>
    exact ⟨fun he => h.property.1 (sun_hub_eq_iff.mp he).1,
      fun he => h.property.2 (sun_hub_eq_iff.mp he).1⟩
  | joint j side =>
    cases j with
    | inl j => simp [cancelPort, Kept]
    | inr rim => cases rim <;> cases side <;> simp [cancelPort, Kept, sun_hub_eq_iff]

noncomputable def cancelPortInv (x : Subtype s.Kept) : s.CancelDart :=
  match x.val with
  | .top i => .top i
  | .bottom i => .bottom i
  | .joint j side => .joint (.inl j) side
  | .hub h i =>
      if hl : h = s.left then .joint (.inr (i == (2 : Fin 3))) false
      else if hr : h = s.right then .joint (.inr (i == (2 : Fin 3))) true
      else .hub ⟨h, hl, hr⟩ i

theorem cancelPort_left_inv (x : s.CancelDart) :
    s.cancelPortInv ⟨s.cancelPort x, s.cancelPort_kept x⟩ = x := by
  cases x with
  | top i => rfl
  | bottom i => rfl
  | hub h i => simp [cancelPortInv, cancelPort, h.property.1, h.property.2]
  | joint j side =>
    cases j with
    | inl j => rfl
    | inr rim => cases rim <;> cases side <;>
        simp [cancelPortInv, cancelPort, s.distinct.symm]

theorem cancelPort_right_inv (x : Subtype s.Kept) : s.cancelPort (s.cancelPortInv x) = x.val := by
  rcases x with ⟨x, hx⟩
  cases x with
  | top i => rfl
  | bottom i => rfl
  | joint j side => rfl
  | hub h i =>
    change Fin 3 at i
    by_cases hl : h = s.left
    · subst h
      have hi : i ≠ 0 := fun he => hx.1 (by rw [he])
      fin_cases i <;> simp_all [cancelPortInv, cancelPort]
    · by_cases hr : h = s.right
      · subst h
        have hi : i ≠ 0 := fun he => hx.2 (by rw [he])
        fin_cases i <;> simp_all [cancelPortInv, cancelPort]
      · simp [cancelPortInv, cancelPort, hl, hr]

noncomputable def cancelPorts : s.CancelDart ≃ Subtype s.Kept where
  toFun x := ⟨s.cancelPort x, s.cancelPort_kept x⟩
  invFun := s.cancelPortInv
  left_inv := s.cancelPort_left_inv
  right_inv x := Subtype.ext (s.cancelPort_right_inv x)

def cancelJointLabel : G.Joint ⊕ Bool → Fin n ⊕ Fin n
  | .inl j => G.jointLabel j
  | .inr false => .inr (G.hubLabel s.left)
  | .inr true => .inr (finRotate n (G.hubLabel s.left))

theorem cancelPort_label (x : s.CancelDart) :
    Port.label G.jointLabel (s.cancelPort x) = Port.label s.cancelJointLabel x := by
  cases x with
  | top i => rfl
  | bottom i => rfl
  | hub h i => rfl
  | joint j side =>
    cases j with
    | inl j => rfl
    | inr rim =>
      cases rim <;> cases side <;>
        change Sum.inr _ = Sum.inr _
      · rfl
      · exact congrArg Sum.inr s.labels.symm
      · rfl
      · exact congrArg (fun j => Sum.inr (finRotate n j)) s.labels.symm

@[reducible] noncomputable def cancel : PortGraph (sunPresentation n b) u v where
  Hub := s.CancelHub
  Joint := G.Joint ⊕ Bool
  hubLabel h := G.hubLabel h.val
  hubFlip h := G.hubFlip h.val
  jointLabel := s.cancelJointLabel
  pairing := (G.pairing.restrict s.Kept (fun _ hx => s.twin_kept hx)).transport
    s.cancelPorts.symm _ (by
      intro x
      obtain ⟨y, rfl⟩ := s.cancelPorts.surjective x
      rw [Equiv.symm_apply_apply]
      exact (s.cancelPort_label y).symm)

theorem cancel_twin (x : s.cancel.Dart) :
    s.cancelPort (s.cancel.pairing.twin x) = G.pairing.twin (s.cancelPort x) := by
  have he := congrArg Subtype.val (s.cancelPorts.apply_symm_apply
    ((G.pairing.restrict s.Kept (fun _ hx => s.twin_kept hx)).twin (s.cancelPorts x)))
  exact he

theorem cancel_character (j : Fin n) : s.cancel.character j = G.character j := by
  rw [s.cancel.sun_character, G.sun_character]

theorem cancel_sign : s.cancel.sign = G.sign := by
  rw [s.cancel.sign_eq_character, G.sign_eq_character]
  simp only [s.cancel_character]

theorem cancel_hub_card : Fintype.card s.cancel.Hub + 2 = Fintype.card G.Hub := by
  have he := Fintype.card_subtype_eq_or_eq_of_ne s.distinct
  have hc := Fintype.card_subtype_compl (fun h : G.Hub => h = s.left ∨ h = s.right)
  have hp : 2 ≤ Fintype.card G.Hub := by
    rw [← he]
    exact Fintype.card_subtype_le _
  have hm := Fintype.card_congr (Equiv.subtypeEquivRight
    (fun h : G.Hub => (not_or : ¬ (h = s.left ∨ h = s.right) ↔ _)))
  rw [he] at hc
  change Fintype.card {h : G.Hub // h ≠ s.left ∧ h ≠ s.right} + 2 = _
  simp only [← Nat.card_eq_fintype_card] at hc hm hp ⊢
  change Nat.card {h : G.Hub // ¬ (h = s.left ∨ h = s.right)} = Nat.card s.CancelHub at hm
  change Nat.card s.CancelHub + 2 = Nat.card G.Hub
  rw [← hm, hc]
  exact Nat.sub_add_cancel hp

theorem cancel_hub_card_lt : Fintype.card s.cancel.Hub < Fintype.card G.Hub := by
  have h := s.cancel_hub_card
  omega

theorem cancel_hub_sum {M : Type*} [AddCommMonoid M] (f : G.Hub → M) :
    (∑ h : s.CancelHub, f h.val) + f s.left + f s.right = ∑ h : G.Hub, f h := by
  rw [← Finset.sum_subtype (p := fun h => h ≠ s.left ∧ h ≠ s.right)
    ((Finset.univ.erase s.left).erase s.right) (by simp [and_comm]) f]
  have hr : s.right ∈ (Finset.univ : Finset G.Hub).erase s.left := by simp [s.distinct.symm]
  calc
    _ = ((∑ h ∈ (Finset.univ.erase s.left).erase s.right, f h) + f s.right) + f s.left := by ac_rfl
    _ = (∑ h ∈ Finset.univ.erase s.left, f h) + f s.left := by
      rw [Finset.sum_erase_add _ f hr]
    _ = ∑ h : G.Hub, f h := Finset.sum_erase_add _ f (Finset.mem_univ s.left)

/-- Exactly the two occurrences at the spoke ends have been removed. -/
theorem cancel_relations :
    (∑ h : s.cancel.Hub, ([s.cancel.hubLabel h] : Multiset (Fin n))) +
      [G.hubLabel s.left, G.hubLabel s.left] =
        ∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin n)) := by
  have h := s.cancel_hub_sum (fun h => ([G.hubLabel h] : Multiset (Fin n)))
  rw [← s.labels, add_assoc] at h
  exact h

end ThomGame.Pictures.PortGraph.SunSpoke
