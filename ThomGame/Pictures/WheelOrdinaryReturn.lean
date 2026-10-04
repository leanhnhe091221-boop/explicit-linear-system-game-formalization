module

public import ThomGame.Pictures.WheelOrdinaryPorts
public import ThomGame.Pictures.ReturnPaths

/-!
# The exact three-step ordinary-port return of a coherently oriented wheel

After entering a wheel through an ordinary port, a face walk visits two
auxiliary ports and then the adjacent ordinary port. Neither intermediate
port is ordinary, so this is the genuine first return. The resulting
vertex permutation reads the original cyclic relation in one orientation.
-/

@[expose] public section
namespace ThomGame.Wheel.Family.GraphLift

open Pictures PortGraph Equiv MarkedReturn

variable {R V R' V' : Type*} {F : Family R V}
  {rows : F.Row ≃ R'} {cols : F.Col ≃ V'}
  {G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] []}
  {r : R} (L : F.GraphLift rows cols G r)

theorem rotation_false (hf : ∀ j k, G.hubFlip (L.hub j k) = false)
    (j : Fin (F.size r)) (k p : Fin 3) :
    G.rotation (.hub (L.hub j k) p) = .hub (L.hub j k) (finRotate 3 p) := by
  rw [G.row_slot_rotation_hub]
  exact congrArg (fun i : Fin 3 => (.hub (L.hub j k) i : G.Dart))
    (by simp [rowSlotRotation, hf])

theorem rotation_true (hf : ∀ j k, G.hubFlip (L.hub j k) = true)
    (j : Fin (F.size r)) (k p : Fin 3) :
    G.rotation (.hub (L.hub j k) p) = .hub (L.hub j k) ((finRotate 3).symm p) := by
  rw [G.row_slot_rotation_hub]
  exact congrArg (fun i : Fin 3 => (.hub (L.hub j k) i : G.Dart))
    (by simp [rowSlotRotation, hf])

theorem ordinaryReturn_false (hf : ∀ j k, G.hubFlip (L.hub j k) = false)
    (j : Fin (F.size r)) :
    F.ordinaryRotation rows cols G (L.ordinaryPort j) =
      L.ordinaryPort ((finRotate (F.size r)).symm j) := by
  let x := (F.ordinaryPairing rows cols G).twin (L.ordinaryPort j)
  let a : G.Dart := .hub (L.hub j 0) (1 : Fin 3)
  let b : G.Dart := .hub (L.hub ((finRotate (F.size r)).symm j) 1) (0 : Fin 3)
  let y := L.ordinaryPort ((finRotate (F.size r)).symm j)
  have h1 : G.circuitStep x.val = a := by
    change G.rotation (G.pairing.twin (G.pairing.twin _)) = _
    rw [G.pairing.involutive]
    exact L.rotation_false hf j 0 0
  have h2 : G.circuitStep a = b := by
    change G.rotation (G.pairing.twin (.hub (L.hub j 0) (1 : Fin 3))) = _
    rw [L.twin_a]
    exact L.rotation_false hf _ 1 2
  have h3 : G.circuitStep b = y.val := by
    have he := (congrArg G.pairing.twin (L.twin_b ((finRotate (F.size r)).symm j))).symm.trans
      (G.pairing.involutive _)
    change G.rotation (G.pairing.twin (.hub (L.hub ((finRotate (F.size r)).symm j) 1) (0 : Fin 3))) = _
    rw [he]
    exact L.rotation_false hf _ 0 2
  have ha : ¬ F.IsOrdinaryPort rows cols G a := by
    intro hh
    exact (by decide : ¬ ((0 : Fin 3) = 0 ∧ (1 : Fin 3) = 0)) ((L.ordinary_port_iff j 0 1).mp hh)
  have hb : ¬ F.IsOrdinaryPort rows cols G b := by
    intro hh
    exact (by decide : ¬ ((1 : Fin 3) = 0 ∧ (0 : Fin 3) = 0)) ((L.ordinary_port_iff _ 1 0).mp hh)
  have hh : Hit G.circuitStep (F.IsOrdinaryPort rows cols G) x.val y.val := by
    apply Hit.skip _ (h1 ▸ ha)
    rw [h1]
    apply Hit.skip _ (h2 ▸ hb)
    rw [h2, ← h3]
    exact Hit.direct _
  exact Subtype.ext (MarkedReturn.eq_perm_of_hit G.circuitStep
    (F.IsOrdinaryPort rows cols G) x y.property hh).symm

theorem ordinaryReturn_true (hf : ∀ j k, G.hubFlip (L.hub j k) = true)
    (j : Fin (F.size r)) :
    F.ordinaryRotation rows cols G (L.ordinaryPort j) =
      L.ordinaryPort (finRotate (F.size r) j) := by
  let x := (F.ordinaryPairing rows cols G).twin (L.ordinaryPort j)
  let a : G.Dart := .hub (L.hub j 0) (2 : Fin 3)
  let b : G.Dart := .hub (L.hub j 1) (2 : Fin 3)
  let y := L.ordinaryPort (finRotate (F.size r) j)
  have h1 : G.circuitStep x.val = a := by
    change G.rotation (G.pairing.twin (G.pairing.twin _)) = _
    rw [G.pairing.involutive]
    exact L.rotation_true hf j 0 0
  have h2 : G.circuitStep a = b := by
    change G.rotation (G.pairing.twin (.hub (L.hub j 0) (2 : Fin 3))) = _
    rw [L.twin_b]
    exact L.rotation_true hf j 1 0
  have h3 : G.circuitStep b = y.val := by
    have he := L.twin_a (finRotate (F.size r) j)
    have hr := congrArg (fun i => (.hub (L.hub i 1) (2 : Fin 3) : G.Dart))
      ((finRotate (F.size r)).symm_apply_apply j)
    have ht := (congrArg G.pairing.twin (he.trans hr)).symm.trans (G.pairing.involutive _)
    change G.rotation (G.pairing.twin (.hub (L.hub j 1) (2 : Fin 3))) = _
    rw [ht]
    exact L.rotation_true hf _ 0 1
  have ha : ¬ F.IsOrdinaryPort rows cols G a := by
    intro hh
    exact (by decide : ¬ ((0 : Fin 3) = 0 ∧ (2 : Fin 3) = 0)) ((L.ordinary_port_iff j 0 2).mp hh)
  have hb : ¬ F.IsOrdinaryPort rows cols G b := by
    intro hh
    exact (by decide : ¬ ((1 : Fin 3) = 0 ∧ (2 : Fin 3) = 0)) ((L.ordinary_port_iff j 1 2).mp hh)
  have hh : Hit G.circuitStep (F.IsOrdinaryPort rows cols G) x.val y.val := by
    apply Hit.skip _ (h1 ▸ ha)
    rw [h1]
    apply Hit.skip _ (h2 ▸ hb)
    rw [h2, ← h3]
    exact Hit.direct _
  exact Subtype.ext (MarkedReturn.eq_perm_of_hit G.circuitStep
    (F.IsOrdinaryPort rows cols G) x y.property hh).symm

theorem ordinaryRotation_apply (b : Bool) (hf : ∀ j k, G.hubFlip (L.hub j k) = b)
    (j : Fin (F.size r)) :
    F.ordinaryRotation rows cols G (L.ordinaryPort j) =
      L.ordinaryPort ((if b then finRotate (F.size r) else (finRotate (F.size r)).symm) j) := by
  cases b
  · exact L.ordinaryReturn_false hf j
  · exact L.ordinaryReturn_true hf j

end ThomGame.Wheel.Family.GraphLift
