module

public import ThomGame.Pictures.CircuitSmoothing

/-!
# Exact accounting for circuits lost during smoothing

Removing a non-loop junction preserves every circuit. Removing an isolated
loop removes exactly the two singleton circuits at its two ports. These are
permutation circuits; no assertion about geometric faces is made here.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped Classical

namespace FiniteReturn

theorem card_remove_one {A : Type*} [Fintype A] (a : A) :
    Fintype.card {x : A // x ≠ a} + 1 = Fintype.card A := by
  have h := Fintype.card_subtype_compl (fun x : A => x = a)
  rw [Fintype.card_subtype_eq] at h
  rw [h]
  have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  omega

theorem card_away_add_two {A : Type*} [Fintype A] {a b : A} (hab : a ≠ b) :
    Fintype.card {x : A // x ≠ a ∧ x ≠ b} + 2 = Fintype.card A := by
  let b' : {x : A // x ≠ a} := ⟨b, hab.symm⟩
  let e : {x : A // x ≠ a ∧ x ≠ b} ≃ {x : {x : A // x ≠ a} // x ≠ b'} := {
    toFun x := ⟨⟨x.val, x.property.1⟩, by
      intro h
      exact x.property.2 (congrArg Subtype.val h)⟩
    invFun x := ⟨x.val.val, x.val.property, by
      intro h
      exact x.property (Subtype.ext h)⟩
    left_inv x := rfl
    right_inv x := rfl }
  have h1 := card_remove_one a
  have h2 := card_remove_one b'
  have he := Nat.card_congr e
  simp only [← Nat.card_eq_fintype_card] at h1 h2 ⊢
  omega

end FiniteReturn

namespace PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

theorem smoothCircuitMap_avoids_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (c : (G.smooth j).Circuit) :
    G.smoothCircuitMap j c ≠ G.circuit (.joint j false) ∧
      G.smoothCircuitMap j c ≠ G.circuit (.joint j true) := by
  refine Quotient.inductionOn c fun x => ?_
  constructor
  · intro h
    have hx := (G.circuit_eq_joint_left_of_loop j hp (G.smoothPortEmbedding j x)).mp h
    exact (G.smoothPorts j x).property.1 hx
  · intro h
    have hx := (G.circuit_eq_joint_right_of_loop j hp (G.smoothPortEmbedding j x)).mp h
    exact (G.smoothPorts j x).property.2 hx

theorem smoothCircuitMap_range_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (c : G.Circuit) :
    (∃ d : (G.smooth j).Circuit, G.smoothCircuitMap j d = c) ↔
      c ≠ G.circuit (.joint j false) ∧ c ≠ G.circuit (.joint j true) := by
  constructor
  · rintro ⟨d, rfl⟩
    exact G.smoothCircuitMap_avoids_loop j hp d
  · refine Quotient.inductionOn c (fun x hx => ?_)
    have hxa : x ≠ .joint j false := by
      intro h
      exact hx.1 (congrArg G.circuit h)
    have hxb : x ≠ .joint j true := by
      intro h
      exact hx.2 (congrArg G.circuit h)
    refine ⟨(G.smooth j).circuit ((G.smoothPorts j).symm ⟨x, hxa, hxb⟩), ?_⟩
    rw [G.smoothCircuitMap_circuit]
    change G.circuit (G.smoothPorts j ((G.smoothPorts j).symm _)).val = G.circuit x
    rw [Equiv.apply_symm_apply]

noncomputable def smoothCircuitComplementEquiv (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    (G.smooth j).Circuit ≃ {c : G.Circuit //
      c ≠ G.circuit (.joint j false) ∧ c ≠ G.circuit (.joint j true)} :=
  Equiv.ofBijective (fun c => ⟨G.smoothCircuitMap j c, G.smoothCircuitMap_avoids_loop j hp c⟩)
    ⟨fun _ _ h => G.smoothCircuitMap_injective j (congrArg Subtype.val h), fun c => by
      obtain ⟨d, hd⟩ := (G.smoothCircuitMap_range_of_loop j hp c.val).mpr c.property
      exact ⟨d, Subtype.ext hd⟩⟩

theorem smooth_circuit_card_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    Fintype.card (G.smooth j).Circuit + 2 = Fintype.card G.Circuit := by
  have he := Fintype.card_congr (G.smoothCircuitComplementEquiv j hp)
  have hc := FiniteReturn.card_away_add_two (G.loop_circuits_ne j hp)
  omega

theorem smooth_circuit_card_of_not_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    Fintype.card (G.smooth j).Circuit = Fintype.card G.Circuit :=
  Fintype.card_congr (G.smoothCircuitEquiv j hp)

theorem smooth_circuit_card (j : G.Joint) :
    Fintype.card (G.smooth j).Circuit + 2 * (G.smoothCircles j).length = Fintype.card G.Circuit := by
  by_cases hp : G.pairing.twin (.joint j false) = .joint j true
  · rw [G.smoothCircles_of_loop j hp]
    exact G.smooth_circuit_card_of_loop j hp
  · rw [G.smoothCircles_of_not_loop j hp]
    simpa using G.smooth_circuit_card_of_not_loop j hp

end PortGraph
end ThomGame.Pictures
