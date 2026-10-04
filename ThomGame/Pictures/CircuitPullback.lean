module

public import ThomGame.Pictures.CircuitEmbedding

/-!
# Pulling a whole circuit back through an actual port embedding

An embedding that preserves edges and equality of incident vertices
reflects every simple circuit whose listed darts lie in its image.
The indexing and both ports at every circuit vertex are retained.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}
  {u v : List S} {w z : List U} {G : PortGraph P u v} {H : PortGraph Q w z}
  (C : H.SimpleCircuit) (e : G.Dart ↪ H.Dart)
  (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
  (ht : ∀ a, H.pairing.twin (e a) = e (G.pairing.twin a))
  (hin : ∀ i : Fin C.length, C.dart i ∈ Set.range e)

noncomputable def pullbackDart (i : Fin C.length) : G.Dart := Classical.choose (hin i)

theorem pullbackDart_image (i : Fin C.length) : e (C.pullbackDart e hin i) = C.dart i :=
  Classical.choose_spec (hin i)

@[reducible] noncomputable def pullback : G.SimpleCircuit where
  length := C.length
  length_pos := C.length_pos
  dart := ⟨C.pullbackDart e hin, by
    intro i j he
    apply C.dart.injective
    exact (C.pullbackDart_image e hin i).symm.trans
      ((congrArg e he).trans (C.pullbackDart_image e hin j))⟩
  vertex_injective := by
    intro i j he
    apply C.vertex_injective
    have hh := (hv _ _).mpr he
    change (e (C.pullbackDart e hin i)).vertex = (e (C.pullbackDart e hin j)).vertex at hh
    simpa only [C.pullbackDart_image e hin] using hh
  edge_injective := by
    intro i j he
    apply C.edge_injective
    apply (H.pairing.edge_eq_iff _ _).mpr
    rcases (G.pairing.edge_eq_iff _ _).mp he with he | he
    · exact Or.inl ((C.pullbackDart_image e hin i).symm.trans
        ((congrArg e he).trans (C.pullbackDart_image e hin j)))
    · apply Or.inr
      exact (C.pullbackDart_image e hin i).symm.trans
        ((congrArg e he).trans ((ht _).symm.trans (congrArg H.pairing.twin (C.pullbackDart_image e hin j))))
  next_vertex := by
    intro i
    apply (hv _ _).mp
    change (e (C.pullbackDart e hin (finRotate C.length i))).vertex =
      (e (G.pairing.twin (C.pullbackDart e hin i))).vertex
    rw [C.pullbackDart_image e hin, ← ht, C.pullbackDart_image e hin]
    exact C.next_vertex i
  next_ne_twin := by
    intro i he
    apply C.next_ne_twin i
    exact (C.pullbackDart_image e hin _).symm.trans
      ((congrArg e he).trans ((ht _).symm.trans (congrArg H.pairing.twin (C.pullbackDart_image e hin i))))

theorem pullback_port (x : Fin C.length × Bool) :
    e ((C.pullback e hv ht hin).port x) = C.port x := by
  rcases x with ⟨i, side⟩
  cases side
  · exact C.pullbackDart_image e hin i
  · change e (G.pairing.twin (C.pullbackDart e hin ((finRotate C.length).symm i))) = _
    rw [← ht, C.pullbackDart_image e hin]
    rfl

end ThomGame.Pictures.PortGraph.SimpleCircuit
