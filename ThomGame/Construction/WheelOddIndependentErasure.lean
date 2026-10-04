module

public import ThomGame.Construction.WheelOddIndependentCut
public import ThomGame.Pictures.SlotErasureEuler

/-!
# Euler saturation and complete smoothing of the independent-rim cut

The new rotation is the genuine first return to the retained ports.
Deleting whole edge pairs therefore preserves Euler saturation. Any
complete smoothing keeps the full character and strictly fewer hubs.
Rim preservation is a separate obligation before using minimality.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (a : H.RimDart (numberedWheelCycles oddWheelCycle)) (hi : OddRimIndependentOnly H a)

theorem oddIndependentCutReturn_joint
    (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) (side : Bool) :
    (MarkedReturn.perm H.rotation (OddIndependentCutKeep a)
      (oddIndependentCutPorts a hi (.joint i side))).val =
        oddIndependentCutPort a (.joint i (!side)) := by
  have hstep :
      H.rotation (oddIndependentCutPort a (.joint i side)) = oddIndependentCutPort a (.joint i (!side)) ∨
      (¬ OddIndependentCutKeep a (H.rotation (oddIndependentCutPort a (.joint i side))) ∧
        H.rotation (H.rotation (oddIndependentCutPort a (.joint i side))) =
          oddIndependentCutPort a (.joint i (!side))) := by
    have hm1 : (-1 : Fin 3) = 2 := by decide +kernel
    cases side <;> cases hf : H.hubFlip ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i)
    all_goals simp [oddIndependentCutPort, H.row_slot_rotation_hub, rowSlotRotation, hf,
      oddIndependentCutKeep_hubAt a hi i, finRotate_apply, finRotate_symm_apply, hm1]
  rcases hstep with he | ⟨hm, he⟩
  · exact (MarkedReturn.perm_val_of_step H.rotation (OddIndependentCutKeep a)
      (oddIndependentCutPorts a hi (.joint i side))
      (he ▸ oddIndependentCutPort_kept a hi (.joint i (!side)))).trans he
  · exact (MarkedReturn.perm_val_of_two_steps H.rotation (OddIndependentCutKeep a)
      (oddIndependentCutPorts a hi (.joint i side)) hm
      (he ▸ oddIndependentCutPort_kept a hi (.joint i (!side)))).trans he

theorem oddIndependentCutGraph_rotation (x : (oddIndependentCutGraph a hi).Dart) :
    MarkedReturn.perm H.rotation (OddIndependentCutKeep a) (oddIndependentCutPorts a hi x) =
      oddIndependentCutPorts a hi ((oddIndependentCutGraph a hi).rotation x) := by
  apply Subtype.ext
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub h p =>
    have he : H.rotation (oddIndependentCutPort a (.hub h p)) =
        oddIndependentCutPort a ((oddIndependentCutGraph a hi).rotation (.hub h p)) := rfl
    exact (MarkedReturn.perm_val_of_step H.rotation (OddIndependentCutKeep a)
      (oddIndependentCutPorts a hi (.hub h p))
      (he ▸ oddIndependentCutPort_kept a hi _)).trans he
  | joint i side => exact oddIndependentCutReturn_joint a hi i side

theorem oddIndependentCutGraph_euler
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    eulerDefect (oddIndependentCutGraph a hi).pairing.perm
      (oddIndependentCutGraph a hi).circuitStep = 0 := by
  let G := oddIndependentCutGraph a hi
  let r := MarkedReturn.perm H.rotation (OddIndependentCutKeep a)
  let t := H.pairing.perm.subtypePerm (oddIndependentCutKeep_twin a hi)
  let e := oddIndependentCutPorts a hi
  have hr : ∀ x, r (e x) = e (G.rotation x) := oddIndependentCutGraph_rotation a hi
  have ht : ∀ x, t (e x) = e (G.pairing.perm x) :=
    fun x => Subtype.ext (oddIndependentCutGraph_twin a hi x).symm
  apply G.rotationEuler_saturated_iff.mp
  rw [RotationEuler.count_congr G.rotation G.pairing.perm r t e hr ht,
    Nat.card_congr (componentCongrEquiv G.rotation G.pairing.perm r t e hr ht)]
  exact RotationEuler.firstReturnRotation_saturated H.rotation (OddIndependentCutKeep a)
    H.pairing.perm (oddIndependentCutKeep_twin a hi) H.pairing.involutive
      (H.rotationEuler_saturated_iff.mpr hEuler)

variable {K : SigmaGraph [] []} {circles : List (Fin 1889684)}
  (t : Smoothing (oddIndependentCutGraph a hi) K circles)

include t in
theorem oddIndependentErasure_euler
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    eulerDefect K.pairing.perm K.circuitStep = 0 :=
  (t.eulerDefect (fun _ => by change 0 < 3; decide +kernel)).trans
    (oddIndependentCutGraph_euler a hi hEuler)

include t in
theorem oddIndependentErasure_character : K.character = H.character := by
  funext r
  exact (t.character r).trans (congrFun (oddIndependentCutGraph_character a hi) r)

include t in
theorem oddIndependentErasure_sign : K.sign = H.sign :=
  t.sign.trans (oddIndependentCutGraph_sign a hi)

include t in
theorem oddIndependentErasure_hub_card :
    Fintype.card K.Hub + (closedSigmaRimCircuit H oddWheelCycle a).length = Fintype.card H.Hub := by
  rw [t.hub_card]
  exact oddIndependentCutGraph_hub_card a hi

include t in
theorem oddIndependentErasure_hub_card_lt : Fintype.card K.Hub < Fintype.card H.Hub :=
  t.hub_card.trans_lt (oddIndependentCutGraph_hub_card_lt a hi)

theorem exists_oddIndependent_erasure
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0) :
    ∃ (K : SigmaGraph [] []) (circles : List (Fin 1889684)),
      Nonempty (Smoothing (oddIndependentCutGraph a hi) K circles) ∧ IsEmpty K.Joint ∧
      eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.character = H.character ∧ K.sign = H.sign ∧
      Fintype.card K.Hub + (closedSigmaRimCircuit H oddWheelCycle a).length = Fintype.card H.Hub ∧
      Fintype.card K.Hub < Fintype.card H.Hub := by
  obtain ⟨K, circles, ⟨t⟩, hJ⟩ := Smoothing.exists_without_junctions (oddIndependentCutGraph a hi)
  exact ⟨K, circles, ⟨t⟩, hJ, oddIndependentErasure_euler a hi t hEuler,
    oddIndependentErasure_character a hi t, oddIndependentErasure_sign a hi t,
    oddIndependentErasure_hub_card a hi t, oddIndependentErasure_hub_card_lt a hi t⟩

end ThomGame.Construction
