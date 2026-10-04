module

public import ThomGame.Pictures.GraphEdges
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Indexed simple circuits in a port graph

A circuit lists one outgoing dart per visited vertex. Its next vertex is
the other endpoint of that dart's edge, with a distinct incoming port.
Edges and vertices are each visited once. A one-edge loop or a two-edge
digon is retained; this definition does not collapse the graph to a
simple graph, and makes no assertion that the circuit bounds a face.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

structure SimpleCircuit where
  length : Nat
  length_pos : 0 < length
  dart : Fin length ↪ G.Dart
  vertex_injective : Function.Injective (fun i => (dart i).vertex)
  edge_injective : Function.Injective (fun i => G.pairing.edge (dart i))
  next_vertex : ∀ i, (dart (finRotate length i)).vertex = (G.pairing.twin (dart i)).vertex
  next_ne_twin : ∀ i, dart (finRotate length i) ≠ G.pairing.twin (dart i)

namespace SimpleCircuit

variable {G} (C : G.SimpleCircuit)

instance : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩

def outgoing (i : Fin C.length) : G.Dart := C.dart i

def incoming (i : Fin C.length) : G.Dart :=
  G.pairing.twin (C.dart ((finRotate C.length).symm i))

theorem incoming_vertex (i : Fin C.length) : (C.incoming i).vertex = (C.outgoing i).vertex := by
  have h := C.next_vertex ((finRotate C.length).symm i)
  simpa only [Equiv.apply_symm_apply, incoming, outgoing] using h.symm

theorem incoming_ne_outgoing (i : Fin C.length) : C.incoming i ≠ C.outgoing i := by
  have h := C.next_ne_twin ((finRotate C.length).symm i)
  simpa only [Equiv.apply_symm_apply, incoming, outgoing] using Ne.symm h

end SimpleCircuit
end ThomGame.Pictures.PortGraph
