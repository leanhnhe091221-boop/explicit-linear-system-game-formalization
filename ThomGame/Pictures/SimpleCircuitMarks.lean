module

public import ThomGame.Pictures.SimpleCircuit
public import ThomGame.Pictures.CircuitPermutations
public import ThomGame.Pictures.MarkedSurgery

/-!
# Marking the ports of a single simple circuit

The marked set consists of the incoming and outgoing ports at each
visited vertex. It is closed under the original edge pairing and has
exactly two ports at each visited vertex. The first return of the
original vertex rotation therefore exchanges these two ports.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv FiniteReturn MarkedReturn

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def port : Fin C.length × Bool → G.Dart
  | (i, false) => C.outgoing i
  | (i, true) => C.incoming i

theorem port_vertex (x : Fin C.length × Bool) : (C.port x).vertex = (C.dart x.1).vertex := by
  rcases x with ⟨i, s⟩
  cases s
  · rfl
  · exact C.incoming_vertex i

theorem port_injective : Function.Injective C.port := by
  rintro ⟨i, s⟩ ⟨j, t⟩ he
  have hi : i = j := C.vertex_injective ((C.port_vertex (i, s)).symm.trans
    ((congrArg Port.vertex he).trans (C.port_vertex (j, t))))
  subst j
  cases s <;> cases t
  · rfl
  · exact (C.incoming_ne_outgoing i he.symm).elim
  · exact (C.incoming_ne_outgoing i he).elim
  · rfl

def Marked (a : G.Dart) : Prop := a ∈ Set.range C.port

noncomputable def portEquiv : Fin C.length × Bool ≃ Subtype C.Marked :=
  Equiv.ofBijective (fun x => ⟨C.port x, ⟨x, rfl⟩⟩)
    ⟨fun _ _ h => C.port_injective (congrArg Subtype.val h), by
      rintro ⟨a, x, hx⟩
      exact ⟨x, Subtype.ext hx⟩⟩

theorem portEquiv_val (x : Fin C.length × Bool) : (C.portEquiv x).val = C.port x := rfl

theorem marked_card : Nat.card (Subtype C.Marked) = 2 * C.length := by
  rw [← Nat.card_congr C.portEquiv, Nat.card_prod, Nat.card_fin]
  simp [Nat.mul_comm]

theorem twin_port (x : Fin C.length × Bool) :
    G.pairing.twin (C.port x) = C.port (CircuitPermutations.edge C.length x) := by
  rcases x with ⟨i, s⟩
  cases s
  · change G.pairing.twin (C.dart i) =
      G.pairing.twin (C.dart ((finRotate C.length).symm (finRotate C.length i)))
    rw [Equiv.symm_apply_apply]
  · exact G.pairing.involutive _

theorem marked_twin_iff (a : G.Dart) : C.Marked (G.pairing.twin a) ↔ C.Marked a := by
  have hm : ∀ b, C.Marked b → C.Marked (G.pairing.twin b) := by
    rintro b ⟨x, rfl⟩
    exact ⟨CircuitPermutations.edge C.length x, (C.twin_port x).symm⟩
  exact ⟨fun h => G.pairing.involutive a ▸ hm _ h, hm a⟩

theorem rotation_return_sameCycle (x y : Fin C.length × Bool) :
    (perm G.rotation C.Marked).SameCycle (C.portEquiv x) (C.portEquiv y) ↔ x.1 = y.1 := by
  rw [sameCycle_iff, G.rotation_sameCycle_iff, portEquiv_val, portEquiv_val,
    C.port_vertex, C.port_vertex]
  exact ⟨fun h => C.vertex_injective h, congrArg (fun i => (C.dart i).vertex)⟩

theorem rotation_return_port (x : Fin C.length × Bool) :
    perm G.rotation C.Marked (C.portEquiv x) =
      C.portEquiv (CircuitPermutations.vertex C.length x) :=
  CircuitPermutations.eq_vertex_of_cycles C.length (perm G.rotation C.Marked)
    C.portEquiv C.rotation_return_sameCycle x

theorem rotation_return_card : Nat.card (Orbit (perm G.rotation C.Marked)) = C.length := by
  rw [← Nat.card_congr (orbitEquiv (CircuitPermutations.vertex C.length)
    (perm G.rotation C.Marked) C.portEquiv C.rotation_return_port),
    CircuitPermutations.vertex_orbit_card]

theorem pairing_return_port (x : Fin C.length × Bool) :
    perm G.pairing.perm C.Marked (C.portEquiv x) =
      C.portEquiv (CircuitPermutations.edge C.length x) := by
  apply Subtype.ext
  have hh : Hit G.pairing.perm C.Marked (C.portEquiv x).val
      (C.portEquiv (CircuitPermutations.edge C.length x)).val := by
    rw [portEquiv_val, portEquiv_val, ← C.twin_port]
    exact Hit.direct _
  exact (eq_perm_of_hit G.pairing.perm C.Marked (C.portEquiv x)
    (C.portEquiv (CircuitPermutations.edge C.length x)).property hh).symm

theorem pairing_return_card : Nat.card (Orbit (perm G.pairing.perm C.Marked)) = C.length := by
  rw [← Nat.card_congr (orbitEquiv (CircuitPermutations.edge C.length)
    (perm G.pairing.perm C.Marked) C.portEquiv C.pairing_return_port),
    CircuitPermutations.edge_orbit_card]

end ThomGame.Pictures.PortGraph.SimpleCircuit
