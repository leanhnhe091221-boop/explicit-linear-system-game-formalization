module

public import ThomGame.Pictures.FiniteReturn
public import ThomGame.Pictures.SmoothedWires

/-!
# First-return circuits after smoothing one junction

The new boundary-circuit permutation is the first return of the old one
to the retained darts, in one or two steps. Thus no retained circuit is
split or merged. Isolated loops require separate accounting below; none
of these combinatorial assertions identifies a circuit with a disk face.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

theorem smooth_circuitStep_val (j : G.Joint) (x : (G.smooth j).Dart) :
    G.smoothPortEmbedding j ((G.smooth j).circuitStep x) =
      G.rotation ((G.pairing.splice (.joint j false) (.joint j true) rfl).twin
        (G.smoothPortEmbedding j x)) := by
  rw [(G.smooth j).circuitStep_apply]
  change (G.smoothPorts j ((G.smooth j).rotation ((G.smooth j).pairing.twin x))).val = _
  rw [G.smooth_rotation, G.smooth_twin_val]
  rfl

theorem smooth_circuit_advances (j : G.Joint) :
    FiniteReturn.Advances G.circuitStep (G.smooth j).circuitStep (G.smoothPortEmbedding j) := by
  classical
  intro x
  let a : G.Dart := .joint j false
  let b : G.Dart := .joint j true
  have hab : a ≠ b := by simp [a, b]
  have hl : Port.label G.jointLabel a = Port.label G.jointLabel b := rfl
  by_cases hxa : G.smoothPortEmbedding j x = G.pairing.twin a
  · have hnext : G.circuitStep (G.smoothPortEmbedding j x) = b := by
      rw [hxa, G.circuitStep_apply, G.pairing.involutive]
      rfl
    refine Or.inr ⟨?_, ?_⟩
    · rw [hnext, G.smooth_circuitStep_val, hxa, G.pairing.splice_twin_partner_left hab hl]
      rfl
    · intro y hy
      rw [hnext] at hy
      exact (G.smoothPorts j y).property.2 hy
  by_cases hxb : G.smoothPortEmbedding j x = G.pairing.twin b
  · have hnext : G.circuitStep (G.smoothPortEmbedding j x) = a := by
      rw [hxb, G.circuitStep_apply, G.pairing.involutive]
      rfl
    refine Or.inr ⟨?_, ?_⟩
    · rw [hnext, G.smooth_circuitStep_val, hxb, G.pairing.splice_twin_partner_right hab hl]
      rfl
    · intro y hy
      rw [hnext] at hy
      exact (G.smoothPorts j y).property.1 hy
  · refine Or.inl ?_
    rw [G.smooth_circuitStep_val]
    exact congrArg G.rotation (G.pairing.splice_twin_unchanged
      (x := G.smoothPortEmbedding j x) hl
      (G.smoothPorts j x).property.1 (G.smoothPorts j x).property.2 hxa hxb)

theorem smooth_sameCycle_iff (j : G.Joint) (a b : (G.smooth j).Dart) :
    (G.smooth j).circuitStep.SameCycle a b ↔
      G.circuitStep.SameCycle (G.smoothPortEmbedding j a) (G.smoothPortEmbedding j b) :=
  (G.smooth_circuit_advances j).sameCycle_iff a b

noncomputable def smoothCircuitMap (j : G.Joint) : (G.smooth j).Circuit → G.Circuit :=
  (G.smooth_circuit_advances j).orbitMap

theorem smoothCircuitMap_circuit (j : G.Joint) (a : (G.smooth j).Dart) :
    G.smoothCircuitMap j ((G.smooth j).circuit a) = G.circuit (G.smoothPortEmbedding j a) := rfl

theorem smoothCircuitMap_injective (j : G.Joint) : Function.Injective (G.smoothCircuitMap j) :=
  (G.smooth_circuit_advances j).orbitMap_injective

noncomputable def smoothCircuitEmbedding (j : G.Joint) : (G.smooth j).Circuit ↪ G.Circuit :=
  ⟨G.smoothCircuitMap j, G.smoothCircuitMap_injective j⟩

theorem circuitStep_joint_left_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    G.circuitStep (.joint j false) = .joint j false := by
  rw [G.circuitStep_apply, hp]
  rfl

theorem circuitStep_joint_right_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    G.circuitStep (.joint j true) = .joint j true := by
  have hp' : G.pairing.twin (.joint j true) = .joint j false := by
    calc
      G.pairing.twin (.joint j true) = G.pairing.twin (G.pairing.twin (.joint j false)) :=
        congrArg G.pairing.twin hp.symm
      _ = _ := G.pairing.involutive _
  rw [G.circuitStep_apply, hp']
  rfl

theorem circuit_eq_joint_left_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (x : G.Dart) :
    G.circuit x = G.circuit (.joint j false) ↔ x = .joint j false := by
  rw [G.circuit_eq_iff]
  constructor
  · intro h
    exact h.eq_of_right (G.circuitStep_joint_left_of_loop j hp)
  · intro h
    exact h.sameCycle G.circuitStep

theorem circuit_eq_joint_right_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (x : G.Dart) :
    G.circuit x = G.circuit (.joint j true) ↔ x = .joint j true := by
  rw [G.circuit_eq_iff]
  constructor
  · intro h
    exact h.eq_of_right (G.circuitStep_joint_right_of_loop j hp)
  · intro h
    exact h.sameCycle G.circuitStep

theorem loop_circuits_ne (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    G.circuit (.joint j false) ≠ G.circuit (.joint j true) := by
  intro h
  have hh := (G.circuit_eq_joint_right_of_loop j hp _).mp h
  cases hh

theorem smoothCircuitMap_surjective_of_not_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    Function.Surjective (G.smoothCircuitMap j) := by
  apply (G.smooth_circuit_advances j).orbitMap_surjective_iff.mpr
  intro x
  by_cases hxa : x = .joint j false
  · subst x
    let z := (G.smoothPorts j).symm
      ⟨G.pairing.twin (.joint j false), G.pairing.partner_left_away hp⟩
    refine ⟨(G.smooth j).rotation z, ?_⟩
    have hz : G.smoothPortEmbedding j ((G.smooth j).rotation z) =
        G.circuitStep (.joint j false) := by
      change (G.smoothPorts j ((G.smooth j).rotation z)).val = _
      rw [G.smooth_rotation]
      simp only [z, Equiv.apply_symm_apply]
      rfl
    rw [hz]
    exact (show G.circuitStep.SameCycle (.joint j false) (G.circuitStep (.joint j false)) from
      ⟨1, by simp⟩).symm
  by_cases hxb : x = .joint j true
  · subst x
    let z := (G.smoothPorts j).symm
      ⟨G.pairing.twin (.joint j true), G.pairing.partner_right_away hp⟩
    refine ⟨(G.smooth j).rotation z, ?_⟩
    have hz : G.smoothPortEmbedding j ((G.smooth j).rotation z) =
        G.circuitStep (.joint j true) := by
      change (G.smoothPorts j ((G.smooth j).rotation z)).val = _
      rw [G.smooth_rotation]
      simp only [z, Equiv.apply_symm_apply]
      rfl
    rw [hz]
    exact (show G.circuitStep.SameCycle (.joint j true) (G.circuitStep (.joint j true)) from
      ⟨1, by simp⟩).symm
  · refine ⟨(G.smoothPorts j).symm ⟨x, hxa, hxb⟩, ?_⟩
    change G.circuitStep.SameCycle (G.smoothPorts j ((G.smoothPorts j).symm _)).val x
    rw [Equiv.apply_symm_apply]

noncomputable def smoothCircuitEquiv (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) :
    (G.smooth j).Circuit ≃ G.Circuit :=
  Equiv.ofBijective (G.smoothCircuitMap j)
    ⟨G.smoothCircuitMap_injective j, G.smoothCircuitMap_surjective_of_not_loop j hp⟩

end ThomGame.Pictures.PortGraph
