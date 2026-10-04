module

public import ThomGame.Pictures.HypergraphDiagram
public import ThomGame.Pictures.Surgery
public import ThomGame.Finite.HypergraphRetractionMap

/-!
# Retraction replacements with fixed boundary

For a trivalent presentation, a hypergraph retraction gives an actual
diagram replacement whenever the boundary lies in its open neighbourhood.
If the neighbourhood has zero vertex labels, the replacement has zero
sign and no more relation vertices. Minimal zero-sign diagrams keep their
size and remain minimal. This concerns explicit diagrams and syntax
frames; it does not identify arbitrary geometric regions with such frames.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S T U : Type*} {P : InvolutionPresentation R S}
  {H : Hypergraph R S} {K : Hypergraph T U}
  (ρ : H.Retraction K)
  (hP : ∀ r, (P.word r : Multiset S) = H.incidence r)
  (hthree : ∀ r, (P.word r).length = 3)

noncomputable def retractionRelabelling : Relabelling P P :=
  .ofGeneralizedHom ρ.endomorphism hP hP hthree

theorem retraction_filterMap {w : List S}
    (hw : ∀ e ∈ w, e ∈ Set.range ρ.inclusion.edge) :
    w.filterMap ρ.endomorphism.edge = w := by
  apply Relabelling.filterMap_eq_of_fixed
  intro e he
  obtain ⟨f, rfl⟩ := hw e he
  exact ρ.endomorphism_edge f

theorem retractionRelabelling_filterMap {w : List S}
    (hw : ∀ e ∈ w, e ∈ Set.range ρ.inclusion.edge) :
    w.filterMap (retractionRelabelling ρ hP hthree).edge = w :=
  retraction_filterMap ρ hw

noncomputable def retractDiagram {u v : List S} (d : Diagram P u v)
    (hu : ∀ e ∈ u, e ∈ Set.range ρ.inclusion.edge)
    (hv : ∀ e ∈ v, e ∈ Set.range ρ.inclusion.edge) : Diagram P u v :=
  ((retractionRelabelling ρ hP hthree).diagram d).cast
    (retractionRelabelling_filterMap ρ hP hthree hu) (retractionRelabelling_filterMap ρ hP hthree hv)

variable {u v : List S} (d : Diagram P u v)
  (hu : ∀ e ∈ u, e ∈ Set.range ρ.inclusion.edge)
  (hv : ∀ e ∈ v, e ∈ Set.range ρ.inclusion.edge)

theorem retractDiagram_size_le : (retractDiagram ρ hP hthree d hu hv).size ≤ d.size := by
  rw [retractDiagram, Diagram.size_cast]
  exact (retractionRelabelling ρ hP hthree).size_diagram_le d

theorem retractDiagram_labels_mem {r : R}
    (hr : r ∈ (retractDiagram ρ hP hthree d hu hv).labels) :
    r ∈ Set.range ρ.inclusion.vertex := by
  rw [retractDiagram, Diagram.labels_cast] at hr
  have hm := ((retractionRelabelling ρ hP hthree).labels_diagram_perm d).mem_iff.mp hr
  obtain ⟨s, _, hs⟩ := List.mem_filterMap.mp hm
  exact ρ.endomorphism_vertex_range hs

theorem retractDiagram_sign_zero
    (hz : ∀ t, P.parity (ρ.inclusion.vertex t) = 0) :
    (retractDiagram ρ hP hthree d hu hv).sign = 0 := by
  rw [retractDiagram, Diagram.sign_cast]
  apply (retractionRelabelling ρ hP hthree).sign_diagram_zero d
  intro r s hs
  obtain ⟨t, rfl⟩ := ρ.endomorphism_vertex_range hs
  exact hz t

theorem retractDiagram_minimal
    (hz : ∀ t, P.parity (ρ.inclusion.vertex t) = 0)
    (hd : d.sign = 0) (hmin : d.Minimal) :
    (retractDiagram ρ hP hthree d hu hv).size = d.size ∧
      (retractDiagram ρ hP hthree d hu hv).Minimal := by
  have hs : (retractDiagram ρ hP hthree d hu hv).sign = d.sign :=
    (retractDiagram_sign_zero ρ hP hthree d hu hv hz).trans hd.symm
  have he : (retractDiagram ρ hP hthree d hu hv).size = d.size :=
    Nat.le_antisymm (retractDiagram_size_le ρ hP hthree d hu hv) (hmin _ hs)
  refine ⟨he, fun e hsign => ?_⟩
  rw [he]
  exact hmin e (hsign.trans hs)

end ThomGame.Pictures
