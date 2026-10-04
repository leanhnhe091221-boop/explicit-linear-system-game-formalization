module

public import ThomGame.Pictures.EmbeddingDiagram
public import ThomGame.Pictures.CharacterMinimal
public import ThomGame.Pictures.RetractionDiagram

/-!
# Minimal diagrams over the actual retracted sun

A minimal zero-sign diagram whose boundary lies in a zero-labelled sun
neighbourhood retracts to a character-minimal sun diagram of the same
size. Every competing sun diagram can be included back with the exact
original boundary and unchanged size, so minimality is proved rather
than required as an extra hypothesis on the retracted diagram.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {H : Hypergraph R S} {n : Nat}
  (ρ : H.Retraction (Hypergraph.sun n))
  (hP : ∀ r, (P.word r : Multiset S) = H.incidence r)
  (hthree : ∀ r, (P.word r).length = 3)

theorem sunRetraction_boundary_map {w : List S}
    (hw : ∀ z ∈ w, z ∈ Set.range ρ.inclusion.edge) :
    (w.filterMap ρ.retract.edge).map ρ.inclusion.edge = w := by
  rw [List.map_filterMap]
  exact retraction_filterMap ρ hw

theorem sunRetraction_boundary_length {w : List S}
    (hw : ∀ z ∈ w, z ∈ Set.range ρ.inclusion.edge) :
    (w.filterMap ρ.retract.edge).length = w.length := by
  have h := congrArg List.length (sunRetraction_boundary_map ρ hw)
  simpa only [List.length_map] using h

theorem sunRetraction_boundary_spokes {w : List S}
    (hw : ∀ z ∈ w, z ∈ Set.range ρ.inclusion.edge)
    (hrim : ∀ j, ρ.inclusion.edge (.inr j) ∉ w) :
    ∀ z ∈ w.filterMap ρ.retract.edge, ∃ j, z = Sum.inl j := by
  intro z hz
  cases z with
  | inl j => exact ⟨j, rfl⟩
  | inr j =>
    apply False.elim
    apply hrim j
    rw [← sunRetraction_boundary_map ρ hw]
    exact List.mem_map.mpr ⟨.inr j, hz, rfl⟩

noncomputable def retractionSunDiagram {u v : List S} (d : Diagram P u v) :
    Diagram (sunPresentation n (fun _ => 0))
      (u.filterMap ρ.retract.edge) (v.filterMap ρ.retract.edge) :=
  (Relabelling.toSun ρ.retract hP (fun _ => 0)).diagram d

theorem retractionSunDiagram_labels_perm {u v : List S} (d : Diagram P u v) :
    (retractionSunDiagram ρ hP d).labels.Perm (d.labels.filterMap ρ.retract.vertex) :=
  (Relabelling.toSun ρ.retract hP (fun _ => 0)).labels_diagram_perm d

theorem retractionSunDiagram_size_le {u v : List S} (d : Diagram P u v) :
    (retractionSunDiagram ρ hP d).size ≤ d.size :=
  (Relabelling.toSun ρ.retract hP (fun _ => 0)).size_diagram_le d

noncomputable def includeRetractionSunDiagram {u v : List S}
    (e : Diagram (sunPresentation n (fun _ => 0))
      (u.filterMap ρ.retract.edge) (v.filterMap ρ.retract.edge))
    (hu : ∀ z ∈ u, z ∈ Set.range ρ.inclusion.edge)
    (hv : ∀ z ∈ v, z ∈ Set.range ρ.inclusion.edge) : Diagram P u v :=
  (embedDiagram ρ.inclusion (sunPresentation_incidence n (fun _ => 0)) hP hthree e).cast
    (sunRetraction_boundary_map ρ hu) (sunRetraction_boundary_map ρ hv)

variable {u v : List S}
  (hu : ∀ z ∈ u, z ∈ Set.range ρ.inclusion.edge)
  (hv : ∀ z ∈ v, z ∈ Set.range ρ.inclusion.edge)

theorem includeRetractionSunDiagram_size
    (e : Diagram (sunPresentation n (fun _ => 0))
      (u.filterMap ρ.retract.edge) (v.filterMap ρ.retract.edge)) :
    (includeRetractionSunDiagram ρ hP hthree e hu hv).size = e.size := by
  rw [includeRetractionSunDiagram, Diagram.size_cast]
  exact embedDiagram_size ρ.inclusion (sunPresentation_incidence n (fun _ => 0)) hP hthree e

theorem includeRetractionSunDiagram_sign_zero
    (e : Diagram (sunPresentation n (fun _ => 0))
      (u.filterMap ρ.retract.edge) (v.filterMap ρ.retract.edge))
    (hz : ∀ j, P.parity (ρ.inclusion.vertex j) = 0) :
    (includeRetractionSunDiagram ρ hP hthree e hu hv).sign = 0 := by
  rw [includeRetractionSunDiagram, Diagram.sign_cast]
  exact embedDiagram_sign_zero ρ.inclusion (sunPresentation_incidence n (fun _ => 0))
    hP hthree e hz

include hthree hu hv in
theorem retractionSunDiagram_minimal (d : Diagram P u v)
    (hz : ∀ j, P.parity (ρ.inclusion.vertex j) = 0)
    (hd : d.sign = 0) (hmin : d.Minimal) :
    (retractionSunDiagram ρ hP d).size = d.size ∧
      (retractionSunDiagram ρ hP d).Minimal ∧
      (retractionSunDiagram ρ hP d).CharacterMinimal := by
  have hbound (e : Diagram (sunPresentation n (fun _ => 0))
      (u.filterMap ρ.retract.edge) (v.filterMap ρ.retract.edge)) : d.size ≤ e.size := by
    have h := hmin (includeRetractionSunDiagram ρ hP hthree e hu hv)
      ((includeRetractionSunDiagram_sign_zero ρ hP hthree hu hv e hz).trans hd.symm)
    rwa [includeRetractionSunDiagram_size] at h
  have hsize := Nat.le_antisymm (retractionSunDiagram_size_le ρ hP d)
    (hbound (retractionSunDiagram ρ hP d))
  have hc : (retractionSunDiagram ρ hP d).CharacterMinimal := by
    intro e _
    rw [hsize]
    exact hbound e
  exact ⟨hsize, ((retractionSunDiagram ρ hP d).sun_minimal_iff_characterMinimal).mpr hc, hc⟩

include hP hthree hu hv in
theorem retractionSunDiagram_retains_labels (d : Diagram P u v)
    (hz : ∀ j, P.parity (ρ.inclusion.vertex j) = 0)
    (hd : d.sign = 0) (hmin : d.Minimal) {r : R} (hr : r ∈ d.labels) :
    ∃ j, ρ.retract.vertex r = some j := by
  have hs := (retractionSunDiagram_minimal ρ hP hthree hu hv d hz hd hmin).1
  have hl : (d.labels.filterMap ρ.retract.vertex).length = d.labels.length :=
    (retractionSunDiagram_labels_perm ρ hP d).length_eq.symm.trans hs
  cases he : ρ.retract.vertex r with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have hlt := List.length_filterMap_lt_length_iff_exists.mpr ⟨r, hr, he⟩
    exact (Nat.ne_of_lt hlt hl).elim

end ThomGame.Pictures
