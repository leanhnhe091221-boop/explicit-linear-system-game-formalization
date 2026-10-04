module

public import ThomGame.Pictures.RowPairInsertionComponents
public import ThomGame.Pictures.RotationEulerGraph

/-!
# Euler saturation of a pair inserted along a single face

The insertion adds two vertices and three edges. The proved face-return
formula adds one face when the selected inputs lie on a common old face.
Old components surject onto new components; the general Euler upper
bound then forces equality of component counts and Euler saturation.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open FiniteReturn RibbonConnectivity
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowPairInsertion) (o : Bool)

theorem vertex_card : Nat.card (s.graph o).Vertex = Nat.card G.Vertex + 2 := by
  change Nat.card ((Fin u.length ⊕ Fin v.length) ⊕ ((G.Hub ⊕ Bool) ⊕ G.Joint)) =
    Nat.card ((Fin u.length ⊕ Fin v.length) ⊕ (G.Hub ⊕ G.Joint)) + 2
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  simp only [Nat.card_sum, hb]
  omega

theorem dart_card : Nat.card (s.graph o).Dart = Nat.card G.Dart + 6 := by
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [← Nat.card_congr s.ports, Nat.card_sum, Nat.card_prod, hb, Nat.card_fin]

theorem edge_card : Nat.card (s.graph o).Edge = Nat.card G.Edge + 3 := by
  have hOld := G.pairing.dart_card_eq_twice_edge_card
  have hNew := (s.graph o).pairing.dart_card_eq_twice_edge_card
  simp only [← Nat.card_eq_fintype_card] at hOld hNew
  change Nat.card G.Dart = 2 * Nat.card G.Edge at hOld
  change Nat.card (s.graph o).Dart = 2 * Nat.card (s.graph o).Edge at hNew
  have hd := s.dart_card o
  omega

theorem eulerCount_preserved
    (hf : G.circuitStep.SameCycle (s.cutLeft o) (s.cutRight o)) :
    eulerCount (s.graph o).pairing.perm (s.graph o).circuitStep =
      eulerCount G.pairing.perm G.circuitStep := by
  have hv := s.vertex_card o
  have he := s.edge_card o
  have hf' := s.face_count_of_same_face o hf
  have hrOld := Nat.card_congr (G.rotationVertexEquiv (fun _ => by change 0 < 3; decide +kernel))
  have hrNew := Nat.card_congr ((s.graph o).rotationVertexEquiv
    (fun _ => by change 0 < 3; decide +kernel))
  have heOld := Nat.card_congr G.edgeOrbitEquiv
  have heNew := Nat.card_congr (s.graph o).edgeOrbitEquiv
  unfold eulerCount
  rw [G.circuit_mul_pairing, (s.graph o).circuit_mul_pairing]
  omega

theorem eulerDefect_eq_zero
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.circuitStep.SameCycle (s.cutLeft o) (s.cutRight o)) :
    eulerDefect (s.graph o).pairing.perm (s.graph o).circuitStep = 0 := by
  have hc := s.component_card_le o
  have he := s.eulerCount_preserved o hf
  have hb := (s.graph o).eulerDefect_nonpos
  unfold eulerDefect at hEuler hb ⊢
  omega

theorem component_card_eq_of_same_face
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.circuitStep.SameCycle (s.cutLeft o) (s.cutRight o)) :
    Nat.card (Component (s.graph o).pairing.perm (s.graph o).circuitStep) =
      Nat.card (Component G.pairing.perm G.circuitStep) := by
  have hn := s.eulerDefect_eq_zero o hEuler hf
  have he := s.eulerCount_preserved o hf
  unfold eulerDefect at hn hEuler
  omega

end ThomGame.Pictures.PortGraph.RowPairInsertion
