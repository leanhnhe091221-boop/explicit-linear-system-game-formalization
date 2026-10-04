module

public import ThomGame.Pictures.DiagramComponentExtraction
public import ThomGame.Pictures.DisconnectedClosedGraph
public import ThomGame.Pictures.InvariantEuler
public import ThomGame.Pictures.CircuitRegionPartition

/-!
# Actual selected components of a closed graph

A vertex selection constant across each edge restricts the original
pairing and rotations to an actual closed port graph. Euler saturation
passes to that invariant subset. Its diagram witness therefore has
exactly the selected relation occurrences, even when the input graph
was not extracted from a diagram.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.Selection

open RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}
    {G : PortGraph P [] []} (c : G.Selection)

def SelectedDart (a : G.Dart) : Prop := c.pick a.vertex = true

abbrev SelectedHub := {h : G.Hub // c.hub h = true}
abbrev SelectedJoint := {j : G.Joint // c.pick (.inr (.inr j)) = true}

noncomputable instance selectedHubFintype : Fintype c.SelectedHub :=
  inferInstanceAs (Fintype {h : G.Hub // c.hub h = true})
noncomputable instance selectedJointFintype : Fintype c.SelectedJoint :=
  inferInstanceAs (Fintype {j : G.Joint // c.pick (.inr (.inr j)) = true})

abbrev SelectedPort :=
  Port P [] [] c.SelectedHub c.SelectedJoint (fun h => G.hubLabel h.val)

def selectedPorts : c.SelectedPort ≃ Subtype c.SelectedDart where
  toFun
    | .top i => i.elim0
    | .bottom i => i.elim0
    | .hub h i => ⟨.hub h.val i, h.property⟩
    | .joint j b => ⟨.joint j.val b, j.property⟩
  invFun a := match a with
    | ⟨.top i, _⟩ => i.elim0
    | ⟨.bottom i, _⟩ => i.elim0
    | ⟨.hub h i, ha⟩ => .hub ⟨h, ha⟩ i
    | ⟨.joint j b, ha⟩ => .joint ⟨j, ha⟩ b
  left_inv a := by
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub _ _ => rfl
    | joint _ _ => rfl
  right_inv a := by
    rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub _ _ => rfl
    | joint _ _ => rfl

theorem selectedDart_rotation (a : G.Dart) :
    c.SelectedDart (G.rotation a) ↔ c.SelectedDart a := by
  simp only [SelectedDart, G.vertex_rotation]

theorem selectedDart_twin (a : G.Dart) :
    c.SelectedDart (G.pairing.twin a) ↔ c.SelectedDart a := by
  simp only [SelectedDart, c.edge]

def selectedPairing :
    Pairing (fun a : Subtype c.SelectedDart => Port.label G.jointLabel a.val) where
  twin a := ⟨G.pairing.twin a.val, (c.selectedDart_twin a.val).mpr a.property⟩
  involutive a := Subtype.ext (G.pairing.involutive a.val)
  ne_self a h := G.pairing.ne_self a.val (congrArg Subtype.val h)
  label_twin a := G.pairing.label_twin a.val

theorem selectedPorts_label (a : c.SelectedPort) :
    Port.label G.jointLabel (c.selectedPorts a).val =
      Port.label (fun j : c.SelectedJoint => G.jointLabel j.val) a := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub _ _ => rfl
  | joint _ _ => rfl

noncomputable def graph : PortGraph P [] [] where
  Hub := c.SelectedHub
  Joint := c.SelectedJoint
  hubLabel h := G.hubLabel h.val
  hubFlip h := G.hubFlip h.val
  jointLabel j := G.jointLabel j.val
  pairing := c.selectedPairing.transport c.selectedPorts.symm
    (Port.label (fun j : c.SelectedJoint => G.jointLabel j.val))
    (fun a => (c.selectedPorts_label (c.selectedPorts.symm a)).symm.trans
      (congrArg (fun x => Port.label G.jointLabel x.val) (c.selectedPorts.apply_symm_apply a)))

theorem graph_rotation (a : c.graph.Dart) :
    (G.rotation.subtypePerm c.selectedDart_rotation) (c.selectedPorts a) =
      c.selectedPorts (c.graph.rotation a) := by
  apply Subtype.ext
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub _ _ => rfl
  | joint _ _ => rfl

theorem graph_pairing (a : c.graph.Dart) :
    (G.pairing.perm.subtypePerm c.selectedDart_twin) (c.selectedPorts a) =
      c.selectedPorts (c.graph.pairing.perm a) := by
  change c.selectedPairing.twin (c.selectedPorts a) =
    c.selectedPorts (c.selectedPorts.symm (c.selectedPairing.twin (c.selectedPorts a)))
  exact (c.selectedPorts.apply_symm_apply _).symm

theorem graph_saturated
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    RotationEuler.count c.graph.rotation c.graph.pairing.perm =
      2 * Nat.card (Component c.graph.rotation c.graph.pairing.perm) := by
  have hs := RotationEuler.subtype_saturated G.rotation G.pairing.perm c.SelectedDart
    c.selectedDart_rotation c.selectedDart_twin G.pairing.involutive hEuler
  have he := RotationEuler.count_congr c.graph.rotation c.graph.pairing.perm
    (G.rotation.subtypePerm c.selectedDart_rotation) (G.pairing.perm.subtypePerm c.selectedDart_twin)
    c.selectedPorts c.graph_rotation c.graph_pairing
  have hc := Nat.card_congr (componentCongrEquiv c.graph.rotation c.graph.pairing.perm
    (G.rotation.subtypePerm c.selectedDart_rotation) (G.pairing.perm.subtypePerm c.selectedDart_twin)
    c.selectedPorts c.graph_rotation c.graph_pairing)
  rw [he, hc]
  exact hs

theorem exists_closed_diagram
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    ∃ d : Diagram P [] [], (d.labels : Multiset R) =
      ∑ h : G.Hub, if c.hub h = true then ([G.hubLabel h] : Multiset R) else 0 := by
  classical
  obtain ⟨d, hd⟩ := c.graph.exists_closed_diagram_of_saturated (fun h => hn h.val)
    (c.graph_saturated hEuler)
  refine ⟨d, hd.trans ?_⟩
  convert SimpleCircuit.subtype_sum_indicator (fun h : G.Hub => c.hub h = true)
    (fun h => ([G.hubLabel h] : Multiset R)) using 1
  · apply Finset.sum_congr
    · ext x
      exact iff_of_true (Finset.mem_univ x)
        (@Finset.mem_univ {h : G.Hub // c.hub h = true}
          (@Subtype.fintype G.Hub (fun h => c.hub h = true)
            (fun h => Classical.propDecidable (c.hub h = true)) G.hubFintype) x)
    · intro x _
      rfl
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : c.hub x = true <;> simp [hx]

end ThomGame.Pictures.PortGraph.Selection
