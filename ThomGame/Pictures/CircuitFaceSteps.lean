module

public import ThomGame.Pictures.CircuitFaces

/-! # Exact face orbits from the actual one-step corner rotations -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem corner_rotation_of_boundsFaceOrbit (side : Bool) (hf : C.BoundsFaceOrbit side)
    (i : Fin C.length) : G.rotation (C.port (i, !side)) = C.port (i, side) := by
  have hm : G.circuitStep.SameCycle (G.pairing.twin (C.port (i, !side))) (C.port (0, side)) := by
    rw [C.twin_port]
    apply (hf _).mpr
    cases side <;> exact ⟨_, rfl⟩
  have hs : G.circuitStep (G.pairing.twin (C.port (i, !side))) = G.rotation (C.port (i, !side)) := by
    rw [G.circuitStep_apply, G.pairing.involutive]
  obtain ⟨j, hj⟩ := (hf _).mp (hs ▸ hm.apply_left)
  have hv := (congrArg Port.vertex hj).trans
    ((G.vertex_rotation _).trans (C.port_vertex (i, !side)))
  have he : j = i := C.vertex_injective ((C.port_vertex (j, side)).symm.trans hv)
  exact hj.symm.trans (congrArg (fun k => C.port (k, side)) he)

theorem boundsFaceOrbit_of_step (side : Bool) (f : Perm (Fin C.length))
    (hf : ∀ i, f.SameCycle 0 i)
    (hstep : ∀ i, G.circuitStep (C.port (i, side)) = C.port (f i, side)) :
    C.BoundsFaceOrbit side := by
  have hp (k : Nat) (i : Fin C.length) :
      (G.circuitStep ^ k) (C.port (i, side)) = C.port ((f ^ k) i, side) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Perm.mul_apply, ih, hstep, pow_succ', Perm.mul_apply]
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hx.symm.exists_nat_pow_eq
    exact ⟨(f ^ k) 0, (hp k 0).symm.trans hk⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := (hf i).exists_nat_pow_eq
    apply Perm.SameCycle.symm
    exact ⟨(k : Int), by rw [zpow_natCast, hp, hk]⟩

/-- A single actual rotation through every corner certifies the whole
face orbit. No Euler or global topological assumption is required. -/
theorem boundsFaceOrbit_of_corner_rotation (side : Bool)
    (hr : ∀ i, G.rotation (C.port (i, !side)) = C.port (i, side)) :
    C.BoundsFaceOrbit side := by
  cases side
  · apply C.boundsFaceOrbit_of_step false (finRotate C.length)
      (fun i => finRotate_sameCycle 0 i)
    intro i
    rw [G.circuitStep_apply, C.twin_port]
    exact hr (finRotate C.length i)
  · apply C.boundsFaceOrbit_of_step true (finRotate C.length).symm
      (fun i => (finRotate_sameCycle 0 i).inv)
    intro i
    rw [G.circuitStep_apply, C.twin_port]
    exact hr ((finRotate C.length).symm i)

end ThomGame.Pictures.PortGraph.SimpleCircuit
