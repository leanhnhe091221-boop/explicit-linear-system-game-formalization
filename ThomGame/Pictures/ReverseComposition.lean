module

public import ThomGame.Pictures.BoundarySwapGraph
public import ThomGame.Pictures.CircuitLocalEmbedding

/-!
# Reversing the order of composition while exchanging boundary names

The two summands exchange positions. Every seam joint stays at its
original boundary index, with its two ports interchanged. Pairing,
rotation, labels, and incidence are preserved on the actual graphs.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}
  (G : PortGraph P u v) (H : PortGraph P v w)

def reverseCompPorts : (G.comp H).Dart ≃ (H.swapBoundary.comp G.swapBoundary).Dart :=
  (compPorts G H).symm.trans ((Equiv.sumComm G.Dart H.Dart).trans
    ((Equiv.sumCongr H.swapBoundaryPorts G.swapBoundaryPorts).trans
      (compPorts H.swapBoundary G.swapBoundary)))

theorem reverseCompPorts_left (x : G.Dart) :
    reverseCompPorts G H (compPorts G H (.inl x)) =
      compPorts H.swapBoundary G.swapBoundary (.inr (G.swapBoundaryPorts x)) := by
  change compPorts H.swapBoundary G.swapBoundary
    ((Equiv.sumCongr H.swapBoundaryPorts G.swapBoundaryPorts)
      ((Equiv.sumComm G.Dart H.Dart) ((compPorts G H).symm (compPorts G H (.inl x))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem reverseCompPorts_right (x : H.Dart) :
    reverseCompPorts G H (compPorts G H (.inr x)) =
      compPorts H.swapBoundary G.swapBoundary (.inl (H.swapBoundaryPorts x)) := by
  change compPorts H.swapBoundary G.swapBoundary
    ((Equiv.sumCongr H.swapBoundaryPorts G.swapBoundaryPorts)
      ((Equiv.sumComm G.Dart H.Dart) ((compPorts G H).symm (compPorts G H (.inr x))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem reverseCompPorts_seam (i : Fin v.length) (b : Bool) :
    reverseCompPorts G H (.joint (.inr i) b) = .joint (.inr i) (!b) := by cases b <;> rfl

theorem reverseCompPorts_pairing (x : (G.comp H).Dart) :
    (H.swapBoundary.comp G.swapBoundary).pairing.twin (reverseCompPorts G H x) =
      reverseCompPorts G H ((G.comp H).pairing.twin x) := by
  obtain ⟨x, rfl⟩ := (compPorts G H).surjective x
  rcases x with x | x
  · rw [reverseCompPorts_left, twin_compPorts, twin_compPorts]
    change compPorts H.swapBoundary G.swapBoundary (.inr (G.swapBoundary.pairing.twin (G.swapBoundaryPorts x))) = _
    change _ = reverseCompPorts G H (compPorts G H (.inl (G.pairing.twin x)))
    rw [reverseCompPorts_left G H (G.pairing.twin x)]
    exact congrArg (fun x => compPorts H.swapBoundary G.swapBoundary (.inr x)) (G.swapBoundary_pairing x)
  · rw [reverseCompPorts_right, twin_compPorts, twin_compPorts]
    change compPorts H.swapBoundary G.swapBoundary (.inl (H.swapBoundary.pairing.twin (H.swapBoundaryPorts x))) = _
    change _ = reverseCompPorts G H (compPorts G H (.inr (H.pairing.twin x)))
    rw [reverseCompPorts_right G H (H.pairing.twin x)]
    exact congrArg (fun x => compPorts H.swapBoundary G.swapBoundary (.inl x)) (H.swapBoundary_pairing x)

theorem reverseCompPorts_rotation (x : (G.comp H).Dart) :
    (H.swapBoundary.comp G.swapBoundary).rotation (reverseCompPorts G H x) =
      reverseCompPorts G H ((G.comp H).rotation x) := by
  cases x with
  | top i => rfl
  | bottom i => rfl
  | hub h i => cases h <;> rfl
  | joint j b => rcases j with (j | j) | i <;> cases b <;> rfl

theorem reverseCompPorts_label (x : (G.comp H).Dart) :
    Port.label (H.swapBoundary.comp G.swapBoundary).jointLabel (reverseCompPorts G H x) =
      Port.label (G.comp H).jointLabel x := by
  cases x with
  | top i => rfl
  | bottom i => rfl
  | hub h i => cases h <;> rfl
  | joint j b => rcases j with (j | j) | i <;> cases b <;> rfl

theorem reverseCompPorts_terminal (x : (G.comp H).Dart) :
    (H.swapBoundary.comp G.swapBoundary).Terminal (reverseCompPorts G H x) ↔ (G.comp H).Terminal x := by
  cases x with
  | top i => rfl
  | bottom i => rfl
  | hub h i => cases h <;> rfl
  | joint j b => rcases j with (j | j) | i <;> cases b <;> rfl

theorem reverseCompPorts_vertices (x y : (G.comp H).Dart) :
    (reverseCompPorts G H x).vertex = (reverseCompPorts G H y).vertex ↔ x.vertex = y.vertex :=
  vertex_iff_of_rotation_equiv (reverseCompPorts G H) (reverseCompPorts_rotation G H) x y

theorem reverseCompPorts_step (x : (G.comp H).Dart) :
    (H.swapBoundary.comp G.swapBoundary).circuitStep (reverseCompPorts G H x) =
      reverseCompPorts G H ((G.comp H).circuitStep x) := by
  rw [(H.swapBoundary.comp G.swapBoundary).circuitStep_apply, reverseCompPorts_pairing,
    reverseCompPorts_rotation]
  rfl

namespace SimpleCircuit

variable (C : (G.comp H).SimpleCircuit)

def reverseComposition : (H.swapBoundary.comp G.swapBoundary).SimpleCircuit :=
  C.mapAlong (reverseCompPorts G H).toEmbedding (reverseCompPorts_vertices G H)
    (fun i => reverseCompPorts_pairing G H (C.dart i))

theorem reverseComposition_port (x : Fin C.length × Bool) :
    (C.reverseComposition G H).port x = reverseCompPorts G H (C.port x) :=
  C.mapAlong_port (reverseCompPorts G H).toEmbedding (reverseCompPorts_vertices G H)
    (fun i => reverseCompPorts_pairing G H (C.dart i)) x

theorem reverseComposition_face (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (C.reverseComposition G H).BoundsFaceOrbit side :=
  C.boundsFaceOrbit_mapAlong (reverseCompPorts G H).toEmbedding (reverseCompPorts_vertices G H)
    (fun i => reverseCompPorts_pairing G H (C.dart i)) side hf
    (fun i => reverseCompPorts_step G H (C.port (i, side)))

end SimpleCircuit
end ThomGame.Pictures.PortGraph
