module

public import ThomGame.Pictures.BoundaryQuadReplacement
public import ThomGame.Pictures.CircuitCompositionFaces

/-!
# An outer-quadrilateral replacement inside an actual closed composition

The port equivalence extends across the unchanged complementary graph.
It fixes every numbered seam and preserves all vertex incidences.
On each retained outer-quadrilateral edge it preserves labels and
pairing; its forward face steps also commute across the seams.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace BoundaryQuadReplacement

variable {G H : PortGraph P u v} (r : G.BoundaryQuadReplacement H)

theorem boundary_iff (x : G.Dart) : H.IsBoundary (r.ports x) ↔ G.IsBoundary x := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := H.boundaryPorts.surjective ⟨r.ports x, hx⟩
    have he : H.boundaryDart j = r.ports x := congrArg Subtype.val hj
    have ho : G.boundaryDart j = x := r.ports.injective ((r.boundary j).trans he)
    exact ho ▸ (G.boundaryPorts j).property
  · intro hx
    obtain ⟨j, hj⟩ := G.boundaryPorts.surjective ⟨x, hx⟩
    have he : G.boundaryDart j = x := congrArg Subtype.val hj
    rw [← he, r.boundary]
    exact (H.boundaryPorts j).property

end BoundaryQuadReplacement

variable (E : PortGraph P [] v) (G H : PortGraph P v [])

theorem compLeftRight_vertex (x : E.Dart) (y : G.Dart) :
    (compLeftEmbedding E G x).vertex = (compRightEmbedding E G y).vertex ↔
      ∃ j : Fin v.length, x = .bottom j ∧ y = .top j := by
  change (compPorts E G (.inl x)).vertex = (compPorts E G (.inr y)).vertex ↔ _
  rw [compPorts_vertex_left, compPorts_vertex_right]
  cases x <;> cases y <;> simp [compVertexLeft, compVertexRight, Port.vertex, comp, eq_comm]

namespace BoundaryQuadReplacement

variable {G H} (r : G.BoundaryQuadReplacement H)

def gluedPorts : (E.comp G).Dart ≃ (E.comp H).Dart :=
  (compPorts E G).symm.trans ((Equiv.sumCongr (Equiv.refl E.Dart) r.ports).trans (compPorts E H))

theorem gluedPorts_comp (x : E.Dart ⊕ G.Dart) :
    r.gluedPorts E (compPorts E G x) = compPorts E H (Sum.map id r.ports x) := by
  change compPorts E H (Equiv.sumCongr (Equiv.refl _) r.ports ((compPorts E G).symm (compPorts E G x))) = _
  rw [Equiv.symm_apply_apply]
  cases x <;> rfl

theorem gluedPorts_left (x : E.Dart) :
    r.gluedPorts E (compLeftEmbedding E G x) = compLeftEmbedding E H x := r.gluedPorts_comp E (.inl x)

theorem gluedPorts_right (x : G.Dart) :
    r.gluedPorts E (compRightEmbedding E G x) = compRightEmbedding E H (r.ports x) :=
  r.gluedPorts_comp E (.inr x)

theorem gluedPorts_vertices (x y : (E.comp G).Dart) :
    (r.gluedPorts E x).vertex = (r.gluedPorts E y).vertex ↔ x.vertex = y.vertex := by
  obtain ⟨x, rfl⟩ := (compPorts E G).surjective x
  obtain ⟨y, rfl⟩ := (compPorts E G).surjective y
  rw [r.gluedPorts_comp, r.gluedPorts_comp]
  rcases x with x | x <;> rcases y with y | y
  · exact (compLeftEmbedding_vertex E H x y).trans (compLeftEmbedding_vertex E G x y).symm
  · change (compLeftEmbedding E H x).vertex = (compRightEmbedding E H (r.ports y)).vertex ↔
      (compLeftEmbedding E G x).vertex = (compRightEmbedding E G y).vertex
    rw [compLeftRight_vertex, compLeftRight_vertex]
    apply exists_congr
    intro j
    have hb : r.ports (.top j) = (.top j : H.Dart) := r.boundary (.inl j)
    rw [← hb, r.ports.injective.eq_iff]
  · change (compRightEmbedding E H (r.ports x)).vertex = (compLeftEmbedding E H y).vertex ↔
      (compRightEmbedding E G x).vertex = (compLeftEmbedding E G y).vertex
    rw [eq_comm, compLeftRight_vertex, eq_comm (a := (compRightEmbedding E G x).vertex), compLeftRight_vertex]
    apply exists_congr
    intro j
    have hb : r.ports (.top j) = (.top j : H.Dart) := r.boundary (.inl j)
    rw [← hb, r.ports.injective.eq_iff]
  · exact (compRightEmbedding_vertex E H (r.ports x) (r.ports y)).trans
      ((r.vertices x y).trans (compRightEmbedding_vertex E G x y).symm)

theorem seamSwap_map (x : E.Dart ⊕ G.Dart) :
    seamSwap E H (Sum.map id r.ports x) = Sum.map id r.ports (seamSwap E G x) := by
  rcases x with x | x
  · cases x with
    | top j => exact j.elim0
    | bottom j =>
      have hb : r.ports (.top j) = (.top j : H.Dart) := r.boundary (.inl j)
      exact congrArg Sum.inr hb.symm
    | hub h j => rfl
    | joint j b => rfl
  · by_cases hx : G.IsBoundary x
    · obtain ⟨j, hj⟩ := G.boundaryPorts.surjective ⟨x, hx⟩
      have he : G.boundaryDart j = x := congrArg Subtype.val hj
      rw [← he]
      cases j with
      | inl j =>
        have hb : r.ports (.top j) = (.top j : H.Dart) := r.boundary (.inl j)
        change seamSwap E H (.inr (r.ports (.top j))) = .inl (.bottom j)
        rw [hb]
        rfl
      | inr j => exact j.elim0
    · have hy : ¬ H.IsBoundary (r.ports x) := fun h => hx ((r.boundary_iff x).mp h)
      have hsG : seamSwap E G (.inr x) = .inr x := by
        cases x <;> first | rfl | exact (hx trivial).elim
      have hsH : seamSwap E H (.inr (r.ports x)) = .inr (r.ports x) := by
        generalize he : r.ports x = y at hy ⊢
        cases y <;> first | rfl | exact (hy trivial).elim
      exact hsH.trans (congrArg (Sum.map id r.ports) hsG).symm

theorem gluedPorts_left_pair (x : E.Dart) :
    (E.comp H).pairing.twin (r.gluedPorts E (compLeftEmbedding E G x)) =
      r.gluedPorts E ((E.comp G).pairing.twin (compLeftEmbedding E G x)) := by
  rw [r.gluedPorts_left, compLeftEmbedding_twin, compLeftEmbedding_twin, r.gluedPorts_left]

theorem gluedPorts_right_pair (x : G.Dart)
    (hx : H.pairing.twin (r.ports x) = r.ports (G.pairing.twin x)) :
    (E.comp H).pairing.twin (r.gluedPorts E (compRightEmbedding E G x)) =
      r.gluedPorts E ((E.comp G).pairing.twin (compRightEmbedding E G x)) := by
  rw [r.gluedPorts_right, compRightEmbedding_twin, compRightEmbedding_twin, r.gluedPorts_right, hx]

theorem gluedPorts_left_step (x : E.Dart) :
    (E.comp H).circuitStep (r.gluedPorts E (compLeftEmbedding E G x)) =
      r.gluedPorts E ((E.comp G).circuitStep (compLeftEmbedding E G x)) := by
  change (E.comp H).circuitStep (r.gluedPorts E (compPorts E G (.inl x))) =
    r.gluedPorts E ((E.comp G).circuitStep (compPorts E G (.inl x)))
  rw [r.gluedPorts_comp, circuitStep_compPorts, circuitStep_compPorts, r.gluedPorts_comp]
  exact congrArg (compPorts E H) (r.seamSwap_map E (.inl (E.circuitStep x)))

theorem gluedPorts_right_step (x : G.Dart)
    (hx : H.circuitStep (r.ports x) = r.ports (G.circuitStep x)) :
    (E.comp H).circuitStep (r.gluedPorts E (compRightEmbedding E G x)) =
      r.gluedPorts E ((E.comp G).circuitStep (compRightEmbedding E G x)) := by
  change (E.comp H).circuitStep (r.gluedPorts E (compPorts E G (.inr x))) =
    r.gluedPorts E ((E.comp G).circuitStep (compPorts E G (.inr x)))
  rw [r.gluedPorts_comp, circuitStep_compPorts, circuitStep_compPorts, r.gluedPorts_comp]
  change compPorts E H (seamSwap E H (.inr (H.circuitStep (r.ports x)))) = _
  rw [hx]
  exact congrArg (compPorts E H) (r.seamSwap_map E (.inr (G.circuitStep x)))

end BoundaryQuadReplacement
end ThomGame.Pictures.PortGraph
