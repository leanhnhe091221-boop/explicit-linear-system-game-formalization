module

public import ThomGame.Pictures.CircuitEmbedding
public import ThomGame.Pictures.CircuitComposition
public import ThomGame.Pictures.GraphSelection
public import ThomGame.Pictures.SunRimCover

/-!
# Internal facial covers survive actual boundary gluing

Both summands embed into the explicit vertically composed port graph.
Their simple circuits contain no boundary ports. Consequently an exact
face orbit around any such circuit survives the seam switches, and all
distinct hub labels in a cover are retained. These statements concern
the composed graph itself, independently of a diagram realization.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}
  (G : PortGraph P u v) (H : PortGraph P v w)

def compLeftEmbedding : G.Dart ↪ (G.comp H).Dart :=
  (Function.Embedding.inl).trans (compPorts G H).toEmbedding

def compRightEmbedding : H.Dart ↪ (G.comp H).Dart :=
  (Function.Embedding.inr).trans (compPorts G H).toEmbedding

theorem compLeftEmbedding_twin (a : G.Dart) :
    (G.comp H).pairing.twin (compLeftEmbedding G H a) =
      compLeftEmbedding G H (G.pairing.twin a) := twin_compPorts G H (.inl a)

theorem compRightEmbedding_twin (a : H.Dart) :
    (G.comp H).pairing.twin (compRightEmbedding G H a) =
      compRightEmbedding G H (H.pairing.twin a) := twin_compPorts G H (.inr a)

theorem compLeftEmbedding_vertex (a b : G.Dart) :
    (compLeftEmbedding G H a).vertex = (compLeftEmbedding G H b).vertex ↔
      a.vertex = b.vertex := by
  change (compPorts G H (.inl a)).vertex = (compPorts G H (.inl b)).vertex ↔ _
  rw [compPorts_vertex_left, compPorts_vertex_left]
  cases a <;> cases b <;> simp [compVertexLeft, Port.vertex, comp]

theorem compRightEmbedding_vertex (a b : H.Dart) :
    (compRightEmbedding G H a).vertex = (compRightEmbedding G H b).vertex ↔
      a.vertex = b.vertex := by
  change (compPorts G H (.inr a)).vertex = (compPorts G H (.inr b)).vertex ↔ _
  rw [compPorts_vertex_right, compPorts_vertex_right]
  cases a <;> cases b <;> simp [compVertexRight, Port.vertex, comp]

theorem compLeftEmbedding_label (a : G.Dart) :
    Port.label (G.comp H).jointLabel (compLeftEmbedding G H a) = Port.label G.jointLabel a := by
  cases a <;> rfl

theorem compRightEmbedding_label (a : H.Dart) :
    Port.label (G.comp H).jointLabel (compRightEmbedding G H a) = Port.label H.jointLabel a := by
  cases a <;> rfl

theorem compLeftEmbedding_step (a : G.Dart) (hb : ¬ G.IsBoundary (G.circuitStep a)) :
    (G.comp H).circuitStep (compLeftEmbedding G H a) =
      compLeftEmbedding G H (G.circuitStep a) := by
  change (G.comp H).circuitStep (compPorts G H (.inl a)) = _
  rw [circuitStep_compPorts]
  change compPorts G H (seamSwap G H (.inl (G.circuitStep a))) =
    compPorts G H (.inl (G.circuitStep a))
  congr 1
  generalize hx : G.circuitStep a = x at hb ⊢
  cases x <;> first | rfl | exact (hb trivial).elim

theorem compRightEmbedding_step (a : H.Dart) (hb : ¬ H.IsBoundary (H.circuitStep a)) :
    (G.comp H).circuitStep (compRightEmbedding G H a) =
      compRightEmbedding G H (H.circuitStep a) := by
  change (G.comp H).circuitStep (compPorts G H (.inr a)) = _
  rw [circuitStep_compPorts]
  change compPorts G H (seamSwap G H (.inr (H.circuitStep a))) =
    compPorts G H (.inr (H.circuitStep a))
  congr 1
  generalize hx : H.circuitStep a = x at hb ⊢
  cases x <;> first | rfl | exact (hb trivial).elim

namespace SimpleCircuit

@[reducible] def compLeft (C : G.SimpleCircuit) : (G.comp H).SimpleCircuit :=
  C.map (compLeftEmbedding G H) (compLeftEmbedding_vertex G H) (compLeftEmbedding_twin G H)

@[reducible] def compRight (C : H.SimpleCircuit) : (G.comp H).SimpleCircuit :=
  C.map (compRightEmbedding G H) (compRightEmbedding_vertex G H) (compRightEmbedding_twin G H)

theorem compLeft_port (C : G.SimpleCircuit) (x : Fin C.length × Bool) :
    (C.compLeft G H).port x = compLeftEmbedding G H (C.port x) := C.map_port _ _ _ x

theorem compRight_port (C : H.SimpleCircuit) (x : Fin C.length × Bool) :
    (C.compRight G H).port x = compRightEmbedding G H (C.port x) := C.map_port _ _ _ x

theorem boundsFaceOrbit_compLeft (C : G.SimpleCircuit) (side : Bool)
    (hf : C.BoundsFaceOrbit side) : (C.compLeft G H).BoundsFaceOrbit side := by
  apply C.boundsFaceOrbit_map (compLeftEmbedding G H) (compLeftEmbedding_vertex G H)
    (compLeftEmbedding_twin G H) side hf
  intro i
  apply compLeftEmbedding_step
  have hc := ((hf _).mpr ⟨i, rfl⟩).apply_left
  obtain ⟨j, hj⟩ := (hf _).mp hc
  rw [← hj]
  exact C.port_not_boundary j side

theorem boundsFaceOrbit_compRight (C : H.SimpleCircuit) (side : Bool)
    (hf : C.BoundsFaceOrbit side) : (C.compRight G H).BoundsFaceOrbit side := by
  apply C.boundsFaceOrbit_map (compRightEmbedding G H) (compRightEmbedding_vertex G H)
    (compRightEmbedding_twin G H) side hf
  intro i
  apply compRightEmbedding_step
  have hc := ((hf _).mpr ⟨i, rfl⟩).apply_left
  obtain ⟨j, hj⟩ := (hf _).mp hc
  rw [← hj]
  exact C.port_not_boundary j side

theorem isLabelCover_compLeft (C : G.SimpleCircuit) (hc : C.IsLabelCover) :
    (C.compLeft G H).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hi, ht, hn, hl⟩ := hc i
  refine ⟨.inl h, .inl k, p, q, ?_, ?_, fun he => hn (Sum.inl.inj he), hl⟩
  · exact congrArg (compLeftEmbedding G H) hi
  · exact (compLeftEmbedding_twin G H (C.dart i)).trans
      (congrArg (compLeftEmbedding G H) ht)

theorem isLabelCover_compRight (C : H.SimpleCircuit) (hc : C.IsLabelCover) :
    (C.compRight G H).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hi, ht, hn, hl⟩ := hc i
  refine ⟨.inr h, .inr k, p, q, ?_, ?_, fun he => hn (Sum.inr.inj he), hl⟩
  · exact congrArg (compRightEmbedding G H) hi
  · exact (compRightEmbedding_twin G H (C.dart i)).trans
      (congrArg (compRightEmbedding G H) ht)

end SimpleCircuit
end ThomGame.Pictures.PortGraph
