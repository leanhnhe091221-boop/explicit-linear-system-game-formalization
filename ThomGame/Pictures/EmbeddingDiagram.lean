module

public import ThomGame.Pictures.HypergraphDiagram
public import ThomGame.Finite.HypergraphEmbeddingMap

/-!
# Including diagrams along an open hypergraph embedding

All vertices and boundary letters are retained. The actual diagram map
preserves the relation multiset under the vertex embedding, and hence
preserves size exactly. Its sign is computed using the target parity.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S T U : Type*} {P : InvolutionPresentation R S} {Q : InvolutionPresentation T U}
  {H : Hypergraph R S} {K : Hypergraph T U}
  (ι : H.OpenEmbedding K)
  (hP : ∀ r, (P.word r : Multiset S) = H.incidence r)
  (hQ : ∀ t, (Q.word t : Multiset U) = K.incidence t)
  (hthree : ∀ t, (Q.word t).length = 3)

noncomputable def Relabelling.ofOpenEmbedding : Relabelling P Q :=
  .ofGeneralizedHom ι.toGeneralizedHom hP hQ hthree

theorem embedding_filterMap (w : List S) :
    w.filterMap (Relabelling.ofOpenEmbedding ι hP hQ hthree).edge = w.map ι.edge := by
  change w.filterMap (some ∘ ι.edge) = w.map ι.edge
  rw [List.filterMap_eq_map]

noncomputable def embedDiagram {u v : List S} (d : Diagram P u v) :
    Diagram Q (u.map ι.edge) (v.map ι.edge) :=
  ((Relabelling.ofOpenEmbedding ι hP hQ hthree).diagram d).cast
    (embedding_filterMap ι hP hQ hthree u) (embedding_filterMap ι hP hQ hthree v)

variable {u v : List S} (d : Diagram P u v)

theorem embedDiagram_labels_perm :
    (embedDiagram ι hP hQ hthree d).labels.Perm (d.labels.map ι.vertex) := by
  rw [embedDiagram, Diagram.labels_cast]
  have h := (Relabelling.ofOpenEmbedding ι hP hQ hthree).labels_diagram_perm d
  change ((Relabelling.ofOpenEmbedding ι hP hQ hthree).diagram d).labels.Perm
    (d.labels.filterMap (some ∘ ι.vertex)) at h
  rwa [List.filterMap_eq_map] at h

theorem embedDiagram_size : (embedDiagram ι hP hQ hthree d).size = d.size := by
  exact (embedDiagram_labels_perm ι hP hQ hthree d).length_eq.trans (List.length_map _)

theorem embedDiagram_sign :
    (embedDiagram ι hP hQ hthree d).sign = (d.labels.map (Q.parity ∘ ι.vertex)).sum := by
  have h := ((embedDiagram_labels_perm ι hP hQ hthree d).map Q.parity).sum_eq
  simpa only [Diagram.sign, List.map_map] using h

theorem embedDiagram_sign_zero (hz : ∀ r, Q.parity (ι.vertex r) = 0) :
    (embedDiagram ι hP hQ hthree d).sign = 0 := by
  rw [embedDiagram_sign]
  exact List.sum_eq_zero (fun z hz' => by
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hz'
    exact hz r)

end ThomGame.Pictures
