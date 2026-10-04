module

public import ThomGame.Pictures.RowGraphEmbeddingInvariants
public import ThomGame.Pictures.BoundaryQuadCapping

/-!
# Open row embeddings preserve entire boundary quadrilateral certificates

All three darts follow the full port equivalence. Both endpoints retain
their boundary positions and adjacency, and both internal face turns are
preserved. Thus the mapped certificate again bounds an exact capped face.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.BoundaryQuadPath

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} {G : SolutionGroup.RowGraph A u v}
  (q : G.BoundaryQuadPath) (ι : A.hypergraph.OpenEmbedding B.hypergraph)

noncomputable def embedRows : (G.embedRows ι).BoundaryQuadPath where
  start := mapBoundaryIndex ι.edge u v q.start
  finish := mapBoundaryIndex ι.edge u v q.finish
  firstHub := q.firstHub
  secondHub := q.secondHub
  firstSlot := ι.slotEquiv (G.hubLabel q.firstHub) q.firstSlot
  secondSlot := ι.slotEquiv (G.hubLabel q.secondHub) q.secondSlot
  first_step := by
    rw [← G.rowEmbeddingPorts_boundaryDart ι, G.rowEmbeddingPorts_circuitStep ι, q.first_step]
    rfl
  second_step := by
    change (G.embedRows ι).circuitStep (G.rowEmbeddingPorts ι q.middleDart) = _
    rw [G.rowEmbeddingPorts_circuitStep ι, q.second_step]
    rfl
  last_step := by
    change (G.embedRows ι).circuitStep (G.rowEmbeddingPorts ι q.lastDart) = _
    rw [G.rowEmbeddingPorts_circuitStep ι, q.last_step, G.rowEmbeddingPorts_boundaryDart ι]
  boundary_adjacent := (mapBoundaryIndex_cyclic ι.edge u v q.start).trans
    (congrArg (mapBoundaryIndex ι.edge u v) q.boundary_adjacent)
  ends_distinct := fun he => q.ends_distinct ((mapBoundaryIndex ι.edge u v).injective he)
  hubs_distinct := q.hubs_distinct

theorem embedRows_firstDart :
    (q.embedRows ι).firstDart = G.rowEmbeddingPorts ι q.firstDart :=
  (G.rowEmbeddingPorts_boundaryDart ι q.start).symm

theorem embedRows_middleDart :
    (q.embedRows ι).middleDart = G.rowEmbeddingPorts ι q.middleDart := rfl

theorem embedRows_lastDart :
    (q.embedRows ι).lastDart = G.rowEmbeddingPorts ι q.lastDart := rfl

theorem embedRows_darts :
    [(q.embedRows ι).firstDart, (q.embedRows ι).middleDart, (q.embedRows ι).lastDart] =
      [q.firstDart, q.middleDart, q.lastDart].map (G.rowEmbeddingPorts ι) := by
  rw [q.embedRows_firstDart, q.embedRows_middleDart, q.embedRows_lastDart]
  rfl

theorem embedRows_capped_face (x : (G.embedRows ι).Dart) :
    ((G.embedRows ι).cappedRotation * (G.embedRows ι).pairing.perm).SameCycle
      (G.rowEmbeddingPorts ι q.firstDart) x ↔
    x = G.rowEmbeddingPorts ι q.firstDart ∨ x = G.rowEmbeddingPorts ι q.middleDart ∨
      x = G.rowEmbeddingPorts ι q.lastDart := by
  simpa only [q.embedRows_firstDart, q.embedRows_middleDart, q.embedRows_lastDart] using
    (q.embedRows ι).capped_face_iff x

end ThomGame.Pictures.PortGraph.BoundaryQuadPath
