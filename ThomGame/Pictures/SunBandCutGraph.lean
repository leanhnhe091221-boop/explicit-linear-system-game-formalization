module

public import ThomGame.Pictures.SunBandCutPorts

/-!
# The actual graph after deleting a three-label circuit's rim edges

The edge involution is restricted to retained ports. Circuit hubs become
two-port joints and their spokes carry the matching unused rim label.
Every hub character is preserved and the hub count strictly decreases.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

@[reducible] noncomputable def sunBandCutGraph : PortGraph (sunPresentation n b) u v where
  Hub := C.ErasedCircuitHub
  Joint := Fin C.length
  hubLabel h := G.hubLabel h.val
  hubFlip h := G.hubFlip h.val
  jointLabel := C.sunBandCutJointLabel i
  pairing := (C.sunBandCutPairing hn i hband).transport (C.sunBandCutPorts hn i hband).symm _ (by
    intro x
    obtain ⟨y, rfl⟩ := (C.sunBandCutPorts hn i hband).surjective x
    rw [Equiv.symm_apply_apply]
    exact (C.sunBandCutPort_label hn i hband y).symm)

theorem sunBandCutGraph_twin (x : (C.sunBandCutGraph hn i hband).Dart) :
    C.sunBandCutPort i ((C.sunBandCutGraph hn i hband).pairing.twin x) =
      G.pairing.twin (C.sunBandCutPort i x) :=
  congrArg Subtype.val ((C.sunBandCutPorts hn i hband).apply_symm_apply
    ((C.sunBandCutPairing hn i hband).twin (C.sunBandCutPorts hn i hband x)))

theorem sunBandCutGraph_boundary (j : BoundaryIndex u v) :
    C.sunBandCutPort i ((C.sunBandCutGraph hn i hband).boundaryDart j) = G.boundaryDart j := by
  cases j <;> rfl

theorem sunBandCutGraph_rotation_hub (h : C.ErasedCircuitHub) (p : Fin 3) :
    C.sunBandCutPort i ((C.sunBandCutGraph hn i hband).rotation (.hub h p)) =
      G.rotation (.hub h.val p) := rfl

theorem sunBandCutGraph_rotation_joint (k : Fin C.length) (side : Bool) :
    (C.sunBandCutGraph hn i hband).rotation (.joint k side) = .joint k (!side) := rfl

theorem sunBandCutGraph_character (r : Fin n) :
    (C.sunBandCutGraph hn i hband).character r = G.character r := by
  rw [PortGraph.character_eq_sum, G.character_eq_sum]
  exact C.sunBand_erased_weight hn i hband (fun j => if j = r then 1 else 0)

theorem sunBandCutGraph_sign : (C.sunBandCutGraph hn i hband).sign = G.sign :=
  C.sunBand_erased_weight hn i hband b

theorem sunBandCutGraph_hub_card :
    Fintype.card (C.sunBandCutGraph hn i hband).Hub + C.length = Fintype.card G.Hub :=
  C.erasedCircuitHub_card

theorem sunBandCutGraph_hub_card_lt :
    Fintype.card (C.sunBandCutGraph hn i hband).Hub < Fintype.card G.Hub :=
  C.erasedCircuitHub_card_lt

theorem sunBandCutGraph_joint_card : Fintype.card (C.sunBandCutGraph hn i hband).Joint = C.length :=
  Fintype.card_fin C.length

theorem sunBandCutGraph_relations :
    (∑ h : (C.sunBandCutGraph hn i hband).Hub,
      ([(C.sunBandCutGraph hn i hband).hubLabel h] : Multiset (Fin n))) +
      (∑ k : Fin C.length, ([G.hubLabel (C.hubAt k)] : Multiset (Fin n))) =
        ∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin n)) :=
  C.erasedCircuitHub_sum (fun h => ([G.hubLabel h] : Multiset (Fin n)))

end ThomGame.Pictures.PortGraph.SimpleCircuit
