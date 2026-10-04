module

public import ThomGame.Pictures.SunBandErasurePorts
public import ThomGame.Pictures.SmoothingTrace

/-!
# The actual graph obtained by erasing a three-label sun circuit

The circuit's hubs and marked edge ends are removed. Every spoke pair
becomes a two-port joint carrying its two original unused ports. The
original pairing is restricted to unmarked ports and transported along
the proved equivalence. Size decreases strictly, all hub characters and
the sign are unchanged, and the graph admits a full recorded smoothing.
Euler and boundary-order preservation are not assumed or asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

omit [IsEmpty G.Joint] in
theorem sunBandErasure_kept_twin (x : G.Dart) (hx : ¬ C.Marked x) : ¬ C.Marked (G.pairing.twin x) :=
  fun h => hx ((C.marked_twin_iff x).mp h)

@[reducible] noncomputable def sunBandErasureGraph : PortGraph (sunPresentation n b) u v where
  Hub := C.ErasedCircuitHub
  Joint := C.SunBandErasureJoint hn i hband
  hubLabel h := G.hubLabel h.val
  hubFlip h := G.hubFlip h.val
  jointLabel := C.sunBandErasureJointLabel hn i hband
  pairing := (G.pairing.restrict (fun x => ¬ C.Marked x) C.sunBandErasure_kept_twin).transport
    (C.sunBandErasurePorts hn i hband).symm _ (by
      intro x
      obtain ⟨y, rfl⟩ := (C.sunBandErasurePorts hn i hband).surjective x
      rw [Equiv.symm_apply_apply]
      exact (C.sunBandErasurePort_label hn i hband y).symm)

theorem sunBandErasureGraph_twin (x : (C.sunBandErasureGraph hn i hband).Dart) :
    C.sunBandErasurePort hn i hband ((C.sunBandErasureGraph hn i hband).pairing.twin x) =
      G.pairing.twin (C.sunBandErasurePort hn i hband x) :=
  congrArg Subtype.val ((C.sunBandErasurePorts hn i hband).apply_symm_apply
    ((G.pairing.restrict (fun x => ¬ C.Marked x) C.sunBandErasure_kept_twin).twin
      (C.sunBandErasurePorts hn i hband x)))

theorem sunBandErasureGraph_boundary (j : BoundaryIndex u v) :
    C.sunBandErasurePort hn i hband ((C.sunBandErasureGraph hn i hband).boundaryDart j) =
      G.boundaryDart j := by cases j <;> rfl

theorem sunBandErasureGraph_rotation_hub (h : C.ErasedCircuitHub) (p : Fin 3) :
    C.sunBandErasurePort hn i hband ((C.sunBandErasureGraph hn i hband).rotation (.hub h p)) =
      G.rotation (.hub h.val p) := rfl

theorem sunBandErasureGraph_rotation_joint (j : C.SunBandErasureJoint hn i hband) (side : Bool) :
    C.sunBandErasurePort hn i hband ((C.sunBandErasureGraph hn i hband).rotation (.joint j side)) =
      C.sunBandExternalPort i (C.sunBandPartner hn i hband
        ((C.sunBandExternalPairing hn i hband).orderedPorts (j, side))) :=
  congrArg (C.sunBandExternalPort i)
    ((C.sunBandExternalPairing hn i hband).orderedPort_twin j side).symm

theorem sunBandErasureGraph_character (r : Fin n) :
    (C.sunBandErasureGraph hn i hband).character r = G.character r := by
  rw [PortGraph.character_eq_sum, G.character_eq_sum]
  exact C.sunBand_erased_weight hn i hband (fun j => if j = r then 1 else 0)

theorem sunBandErasureGraph_sign : (C.sunBandErasureGraph hn i hband).sign = G.sign :=
  C.sunBand_erased_weight hn i hband b

theorem sunBandErasureGraph_hub_card :
    Fintype.card (C.sunBandErasureGraph hn i hband).Hub + C.length = Fintype.card G.Hub :=
  C.erasedCircuitHub_card

theorem sunBandErasureGraph_hub_card_lt :
    Fintype.card (C.sunBandErasureGraph hn i hband).Hub < Fintype.card G.Hub :=
  C.erasedCircuitHub_card_lt

theorem sunBandErasureGraph_joint_card :
    2 * Fintype.card (C.sunBandErasureGraph hn i hband).Joint = C.length :=
  (C.sunBandExternalPairing hn i hband).card_ordered_edges.symm

theorem sunBandErasureGraph_relations :
    (∑ h : (C.sunBandErasureGraph hn i hband).Hub,
      ([(C.sunBandErasureGraph hn i hband).hubLabel h] : Multiset (Fin n))) +
      (∑ k : Fin C.length, ([G.hubLabel (C.hubAt k)] : Multiset (Fin n))) =
        ∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin n)) :=
  C.erasedCircuitHub_sum (fun h => ([G.hubLabel h] : Multiset (Fin n)))

theorem sunBandErasureGraph_exists_smoothed :
    ∃ (H : PortGraph (sunPresentation n b) u v) (circles : List (Fin n ⊕ Fin n)),
      Nonempty (Smoothing (C.sunBandErasureGraph hn i hband) H circles) ∧ IsEmpty H.Joint ∧
      Fintype.card H.Hub + C.length = Fintype.card G.Hub ∧
      (∀ r, H.character r = G.character r) ∧ H.sign = G.sign := by
  obtain ⟨H, circles, ⟨t⟩, hH⟩ := Smoothing.exists_without_junctions (C.sunBandErasureGraph hn i hband)
  refine ⟨H, circles, ⟨t⟩, hH, ?_, ?_, t.sign.trans (C.sunBandErasureGraph_sign hn i hband)⟩
  · rw [t.hub_card]
    exact C.sunBandErasureGraph_hub_card hn i hband
  · intro r
    exact (t.character r).trans (C.sunBandErasureGraph_character hn i hband r)

end ThomGame.Pictures.PortGraph.SimpleCircuit
