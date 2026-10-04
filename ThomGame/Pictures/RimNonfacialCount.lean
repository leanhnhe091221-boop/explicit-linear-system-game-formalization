module

public import ThomGame.Pictures.RimCircuitUniqueness

/-!
# Counting nonfacial restricted rim components

The count is over the finite component quotient, so changing a circuit
enumeration or its orientation contributes no extra copy. In a saturated
graph, any labelled simple circuit represents the faciality predicate of
its component. Representatives of nonfacial components are nonfacial.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} (G : SolutionGroup.RowGraph A u v) (γ : Hypergraph.Cycle A.hypergraph)
  (hu : ∀ z ∈ u, z ∉ Set.range γ.edge) (hv : ∀ z ∈ v, z ∉ Set.range γ.edge)

def RimComponentFacial (c : G.RimComponent γ hu hv) : Prop :=
  ∃ a : G.RimDart γ, G.rimComponent γ hu hv a = c ∧
    ∃ side, (G.rimSimpleCircuit γ hu hv a).BoundsFaceOrbit side

abbrev NonfacialRimComponent := {c : G.RimComponent γ hu hv // ¬ G.RimComponentFacial γ hu hv c}

noncomputable instance nonfacialRimComponentFintype : Fintype (G.NonfacialRimComponent γ hu hv) :=
  Fintype.ofFinite _

noncomputable def nonfacialRimCount : Nat := Nat.card (G.NonfacialRimComponent γ hu hv)

theorem rimSimpleCircuit_marked_component_iff (a b : G.RimDart γ) :
    (G.rimSimpleCircuit γ hu hv a).Marked b.val ↔
      G.rimComponent γ hu hv b = G.rimComponent γ hu hv a :=
  (G.rimSimpleCircuit γ hu hv a).marked_iff_rimComponent γ hu hv
    (G.rimSimpleCircuit_rim γ hu hv a) b

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem rimComponentFacial_iff_circuit (C : G.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length, Port.label G.jointLabel (C.dart k) ∈ Set.range γ.edge) :
    G.RimComponentFacial γ hu hv (G.rimComponent γ hu hv (C.labelledRimDart γ hlabels 0)) ↔
      ∃ side, C.BoundsFaceOrbit side := by
  let a := C.labelledRimDart γ hlabels 0
  constructor
  · rintro ⟨b, hb, side, hf⟩
    exact C.exists_face_of_common_rim_port γ hu hv hlabels (G.rimSimpleCircuit γ hu hv b)
      (G.rimSimpleCircuit_rim γ hu hv b) hEuler a.val ⟨(0, false), rfl⟩
      ((G.rimSimpleCircuit_marked_component_iff γ hu hv b a).mpr hb.symm) side hf
  · rintro ⟨side, hf⟩
    refine ⟨a, rfl, ?_⟩
    exact (G.rimSimpleCircuit γ hu hv a).exists_face_of_common_rim_port γ hu hv
      (G.rimSimpleCircuit_rim γ hu hv a) C hlabels hEuler a.val
      ⟨(0, false), rfl⟩ ⟨(0, false), rfl⟩ side hf

include hEuler in
theorem rimComponentFacial_iff (a : G.RimDart γ) :
    G.RimComponentFacial γ hu hv (G.rimComponent γ hu hv a) ↔
      ∃ side, (G.rimSimpleCircuit γ hu hv a).BoundsFaceOrbit side :=
  G.rimComponentFacial_iff_circuit γ hu hv hEuler (G.rimSimpleCircuit γ hu hv a)
    (G.rimSimpleCircuit_rim γ hu hv a)

noncomputable def nonfacialRimCircuit (c : G.NonfacialRimComponent γ hu hv) : G.SimpleCircuit :=
  G.rimSimpleCircuit γ hu hv c.val.out

theorem nonfacialRimCircuit_labels (c : G.NonfacialRimComponent γ hu hv)
    (k : Fin (G.nonfacialRimCircuit γ hu hv c).length) :
    Port.label G.jointLabel ((G.nonfacialRimCircuit γ hu hv c).dart k) ∈ Set.range γ.edge :=
  G.rimSimpleCircuit_rim γ hu hv c.val.out k

theorem nonfacialRimCircuit_marked (c : G.NonfacialRimComponent γ hu hv) (a : G.RimDart γ) :
    (G.nonfacialRimCircuit γ hu hv c).Marked a.val ↔ G.rimComponent γ hu hv a = c.val := by
  have ho : G.rimComponent γ hu hv c.val.out = c.val := Quotient.out_eq _
  rw [nonfacialRimCircuit, G.rimSimpleCircuit_marked_component_iff, ho]

include hEuler in
theorem nonfacialRimCircuit_not_face (c : G.NonfacialRimComponent γ hu hv) :
    ¬ ∃ side, (G.nonfacialRimCircuit γ hu hv c).BoundsFaceOrbit side := by
  intro hf
  have hh := (G.rimComponentFacial_iff γ hu hv hEuler c.val.out).mpr hf
  have ho : G.rimComponent γ hu hv c.val.out = c.val := Quotient.out_eq _
  rw [ho] at hh
  exact c.property hh

theorem nonfacialRimComponent_ext (c d : G.NonfacialRimComponent γ hu hv)
    (hm : ∀ x, (G.nonfacialRimCircuit γ hu hv c).Marked x ↔
      (G.nonfacialRimCircuit γ hu hv d).Marked x) : c = d := by
  have hc : (G.nonfacialRimCircuit γ hu hv c).Marked c.val.out.val := ⟨(0, false), rfl⟩
  have hd := (G.nonfacialRimCircuit_marked γ hu hv d c.val.out).mp ((hm _).mp hc)
  apply Subtype.ext
  exact (Quotient.out_eq c.val).symm.trans hd

include hEuler in
theorem nonfacialRimCount_eq_zero_iff : G.nonfacialRimCount γ hu hv = 0 ↔
    ∀ a : G.RimDart γ, ∃ side, (G.rimSimpleCircuit γ hu hv a).BoundsFaceOrbit side := by
  classical
  constructor
  · intro hz a
    by_contra hn
    let c : G.NonfacialRimComponent γ hu hv :=
      ⟨G.rimComponent γ hu hv a, fun hf => hn ((G.rimComponentFacial_iff γ hu hv hEuler a).mp hf)⟩
    have hp : 0 < Fintype.card (G.NonfacialRimComponent γ hu hv) := Fintype.card_pos_iff.mpr ⟨c⟩
    rw [nonfacialRimCount, Nat.card_eq_fintype_card] at hz
    omega
  · intro hf
    have hi : IsEmpty (G.NonfacialRimComponent γ hu hv) :=
      ⟨fun c => c.property ⟨c.val.out, Quotient.out_eq _, hf c.val.out⟩⟩
    let := hi
    simp [nonfacialRimCount]

end ThomGame.Pictures.PortGraph
