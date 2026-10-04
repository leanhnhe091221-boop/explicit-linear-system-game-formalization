module

public import ThomGame.Construction.WheelConstellation
public import ThomGame.Construction.WheelDiagram
public import ThomGame.Pictures.RetractionDiagram

/-!
# Actual wheel retractions applied to numbered solution diagrams

All central cycles and pentagons admit a map to their sun neighbourhood.
For a stellar cycle, re-inclusion gives a zero-sign replacement with the
original boundary whenever that boundary is contained in the neighbourhood.
The exceptional pentagon still has a retraction but is excluded from this
zero-sign assertion.
-/

@[expose] public section
namespace ThomGame.Construction

def numberedWheelCycleRetraction (i : WheelCycleIndex) :
    Hypergraph.Retraction numberedSystem.hypergraph (Hypergraph.sun (wheelCycles i).length) :=
  match i with
  | .inl r => numberedCentralWheelRetraction r
  | .inr ⟨r, j⟩ => numberedPentagonWheelRetraction r j

theorem numberedWheelCycleRetraction_vertex (i : WheelCycleIndex) (k : Fin (wheelCycles i).length) :
    (numberedWheelCycleRetraction i).inclusion.vertex k = rowEquiv ((wheelCycles i).vertex k) := by
  cases i with
  | inl r => rfl
  | inr rj => cases rj; rfl

theorem numberedWheelCycleRetraction_rhs_zero (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    (k : Fin (wheelCycles i).length) :
    numberedSystem.rhs ((numberedWheelCycleRetraction i).inclusion.vertex k) = 0 := by
  rw [numberedWheelCycleRetraction_vertex, numbered_rhs]
  obtain ⟨h⟩ := wheelCycle_stellar_of_ne_odd i hi
  exact h.rhs_zero k

noncomputable def sigmaToCycleSun (i : WheelCycleIndex) :
    Pictures.Relabelling (SolutionGroup.triangularPresentation numberedSystem)
      (Pictures.sunPresentation (wheelCycles i).length (fun _ => 0)) :=
  .toSun (numberedWheelCycleRetraction i).retract (fun _ => rfl) (fun _ => 0)

theorem sigmaToCycleSun_size_le (i : WheelCycleIndex) {u v : List (Fin 1889684)}
    (d : SigmaDiagram u v) : ((sigmaToCycleSun i).diagram d).size ≤ d.size :=
  (sigmaToCycleSun i).size_diagram_le d

theorem sigmaToCycleSun_closed_character (i : WheelCycleIndex) (d : SigmaDiagram [] [])
    (k : Fin (wheelCycles i).length) : ((sigmaToCycleSun i).diagram d).character k = 0 :=
  ((sigmaToCycleSun i).diagram d).closed_sun_character k

noncomputable def retractSigmaDiagram (i : WheelCycleIndex) {u v : List (Fin 1889684)}
    (d : SigmaDiagram u v)
    (hu : ∀ e ∈ u, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hv : ∀ e ∈ v, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge) : SigmaDiagram u v :=
  Pictures.retractDiagram (numberedWheelCycleRetraction i) (fun _ => rfl) (fun _ => rfl) d hu hv

theorem retractSigmaDiagram_size_le (i : WheelCycleIndex) {u v : List (Fin 1889684)}
    (d : SigmaDiagram u v)
    (hu : ∀ e ∈ u, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hv : ∀ e ∈ v, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge) :
    (retractSigmaDiagram i d hu hv).size ≤ d.size :=
  Pictures.retractDiagram_size_le (numberedWheelCycleRetraction i) (fun _ => rfl) (fun _ => rfl) d hu hv

theorem retractSigmaDiagram_sign_zero (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    {u v : List (Fin 1889684)} (d : SigmaDiagram u v)
    (hu : ∀ e ∈ u, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hv : ∀ e ∈ v, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge) :
    (retractSigmaDiagram i d hu hv).sign = 0 :=
  Pictures.retractDiagram_sign_zero (numberedWheelCycleRetraction i) (fun _ => rfl) (fun _ => rfl)
    d hu hv (numberedWheelCycleRetraction_rhs_zero i hi)

theorem retractSigmaDiagram_minimal (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    {u v : List (Fin 1889684)} (d : SigmaDiagram u v)
    (hu : ∀ e ∈ u, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hv : ∀ e ∈ v, e ∈ Set.range (numberedWheelCycleRetraction i).inclusion.edge)
    (hd : d.sign = 0) (hmin : d.Minimal) :
    (retractSigmaDiagram i d hu hv).size = d.size ∧ (retractSigmaDiagram i d hu hv).Minimal :=
  Pictures.retractDiagram_minimal (numberedWheelCycleRetraction i) (fun _ => rfl) (fun _ => rfl)
    d hu hv (numberedWheelCycleRetraction_rhs_zero i hi) hd hmin

end ThomGame.Construction
