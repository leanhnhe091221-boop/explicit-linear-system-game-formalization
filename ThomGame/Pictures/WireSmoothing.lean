module

public import ThomGame.Pictures.GraphWires

/-! # Smoothing preserves exactly the wires between surviving ports -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

noncomputable def bypass (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) (x : G.Dart) : (G.smooth j).Dart :=
  (G.smoothPorts j).symm (if ha : x = .joint j false then
    ⟨G.pairing.twin (.joint j false), G.pairing.partner_left_away hp⟩ else
    if hb : x = .joint j true then
      ⟨G.pairing.twin (.joint j true), G.pairing.partner_right_away hp⟩ else ⟨x, ha, hb⟩)

theorem bypass_away (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true)
    (x : Pairing.Away (Port.joint j false : G.Dart) (.joint j true)) :
    G.bypass j hp x.val = (G.smoothPorts j).symm x := by
  simp [bypass, x.property.1, x.property.2]

theorem bypass_survivor (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true)
    (x : (G.smooth j).Dart) : G.bypass j hp (G.smoothPorts j x).val = x := by
  rw [G.bypass_away, Equiv.symm_apply_apply]

theorem bypass_left (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    G.bypass j hp (.joint j false) =
      (G.smoothPorts j).symm ⟨G.pairing.twin (.joint j false), G.pairing.partner_left_away hp⟩ := by
  simp [bypass]

theorem bypass_right (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    G.bypass j hp (.joint j true) =
      (G.smoothPorts j).symm ⟨G.pairing.twin (.joint j true), G.pairing.partner_right_away hp⟩ := by
  simp [bypass]

theorem bypass_partner_left (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    G.bypass j hp (G.pairing.twin (.joint j false)) = G.bypass j hp (.joint j false) := by
  rw [G.bypass_left]
  exact G.bypass_away j hp ⟨_, G.pairing.partner_left_away hp⟩

theorem bypass_partner_right (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    G.bypass j hp (G.pairing.twin (.joint j true)) = G.bypass j hp (.joint j true) := by
  rw [G.bypass_right]
  exact G.bypass_away j hp ⟨_, G.pairing.partner_right_away hp⟩

theorem bypass_edge (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true)
    (x : G.Dart) : (G.smooth j).WireConnected (G.bypass j hp x) (G.bypass j hp (G.pairing.twin x)) := by
  by_cases hxa : x = .joint j false
  · subst x
    rw [G.bypass_partner_left]
    exact (G.smooth j).wireConnected_refl _
  by_cases hxb : x = .joint j true
  · subst x
    rw [G.bypass_partner_right]
    exact (G.smooth j).wireConnected_refl _
  by_cases hxpa : x = G.pairing.twin (.joint j false)
  · subst x
    rw [G.pairing.involutive, G.bypass_partner_left]
    exact (G.smooth j).wireConnected_refl _
  by_cases hxpb : x = G.pairing.twin (.joint j true)
  · subst x
    rw [G.pairing.involutive, G.bypass_partner_right]
    exact (G.smooth j).wireConnected_refl _
  have hpa : G.pairing.twin x ≠ .joint j false := by
    intro h
    have hh := congrArg G.pairing.twin h
    rw [G.pairing.involutive] at hh
    exact hxpa hh
  have hpb : G.pairing.twin x ≠ .joint j true := by
    intro h
    have hh := congrArg G.pairing.twin h
    rw [G.pairing.involutive] at hh
    exact hxpb hh
  let y : Pairing.Away (Port.joint j false : G.Dart) (.joint j true) := ⟨x, hxa, hxb⟩
  let z : Pairing.Away (Port.joint j false : G.Dart) (.joint j true) := ⟨G.pairing.twin x, hpa, hpb⟩
  have ht : (G.smooth j).pairing.twin ((G.smoothPorts j).symm y) = (G.smoothPorts j).symm z := by
    apply (G.smoothPorts j).injective
    apply Subtype.ext
    rw [G.smooth_twin_val, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact G.pairing.splice_twin_unchanged (a := .joint j false) (b := .joint j true)
      rfl hxa hxb hxpa hxpb
  rw [G.bypass_away j hp y, G.bypass_away j hp z, ← ht]
  exact (G.smooth j).wireConnected_edge _

theorem bypass_joint (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    (G.smooth j).WireConnected (G.bypass j hp (.joint j false)) (G.bypass j hp (.joint j true)) := by
  have ht : (G.smooth j).pairing.twin (G.bypass j hp (.joint j false)) =
      G.bypass j hp (.joint j true) := by
    rw [G.bypass_left, G.bypass_right]
    apply (G.smoothPorts j).injective
    rw [G.smooth_twin, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact G.pairing.smooth_joins_partners (a := .joint j false) (b := .joint j true)
      (by simp) rfl hp
  rw [← ht]
  exact (G.smooth j).wireConnected_edge _

theorem bypass_turn (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true)
    (x : G.Dart) : (G.smooth j).WireConnected (G.bypass j hp x) (G.bypass j hp (G.wireTurn x)) := by
  cases x with
  | top i => exact (G.smooth j).wireConnected_refl _
  | bottom i => exact (G.smooth j).wireConnected_refl _
  | hub h i => exact (G.smooth j).wireConnected_refl _
  | joint k side =>
    by_cases hkj : k = j
    · subst k
      cases side with
      | false => exact G.bypass_joint j hp
      | true => exact (G.smooth j).wireConnected_symm (G.bypass_joint j hp)
    · let y : (G.smooth j).Dart := .joint ⟨k, hkj⟩ side
      have hy : (G.smoothPorts j y).val = .joint k side := rfl
      rw [← hy, ← G.smooth_wireTurn, G.bypass_survivor, G.bypass_survivor]
      exact (G.smooth j).wireConnected_turn y

theorem bypass_wireConnected (j : G.Joint) (hp : G.pairing.twin (.joint j false) ≠ .joint j true)
    {a b : G.Dart} (h : G.WireConnected a b) :
    (G.smooth j).WireConnected (G.bypass j hp a) (G.bypass j hp b) := by
  induction h with
  | refl => exact (G.smooth j).wireConnected_refl _
  | @tail b c hab hbc ih =>
    rcases hbc with rfl | rfl
    · exact (G.smooth j).wireConnected_trans ih (G.bypass_edge j hp b)
    · exact (G.smooth j).wireConnected_trans ih (G.bypass_turn j hp b)

/-- In the isolated-loop case a path starting outside the loop stays outside it. -/
theorem loop_wireConnected_lifts (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (a : (G.smooth j).Dart)
    {b : G.Dart} (h : G.WireConnected (G.smoothPorts j a).val b) :
    ∃ c : (G.smooth j).Dart, (G.smoothPorts j c).val = b ∧ (G.smooth j).WireConnected a c := by
  induction h with
  | refl => exact ⟨a, rfl, (G.smooth j).wireConnected_refl a⟩
  | @tail b c hab hbc ih =>
    obtain ⟨d, hd, ih⟩ := ih
    rcases hbc with rfl | rfl
    · refine ⟨(G.smooth j).pairing.twin d, ?_,
        (G.smooth j).wireConnected_trans ih ((G.smooth j).wireConnected_edge d)⟩
      rw [G.smooth_twin_val, G.pairing.splice_twin_of_paired
        (a := .joint j false) (b := .joint j true) rfl hp, hd]
    · refine ⟨(G.smooth j).wireTurn d, ?_,
        (G.smooth j).wireConnected_trans ih ((G.smooth j).wireConnected_turn d)⟩
      rw [G.smooth_wireTurn, hd]

theorem smooth_wireConnected_iff (j : G.Joint) (a b : (G.smooth j).Dart) :
    (G.smooth j).WireConnected a b ↔
      G.WireConnected (G.smoothPorts j a).val (G.smoothPorts j b).val := by
  constructor
  · exact G.smooth_wireConnected_expands j
  · intro h
    by_cases hp : G.pairing.twin (.joint j false) = .joint j true
    · obtain ⟨c, hc, hh⟩ := G.loop_wireConnected_lifts j hp a h
      have hcb : c = b := (G.smoothPorts j).injective (Subtype.ext hc)
      rwa [hcb] at hh
    · have hh := G.bypass_wireConnected j hp h
      simpa only [G.bypass_survivor] using hh

end ThomGame.Pictures.PortGraph
