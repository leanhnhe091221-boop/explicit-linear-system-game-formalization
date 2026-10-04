module

public import ThomGame.Construction.WheelOddErasurePorts

/-!
# Every surviving labelled circuit is an unchanged original circuit

The recovery keeps its complete indexed ports and labels. An original
facial cover reflects back to the surviving circuit: both the corner
rotations and the distinct labels of each edge's hubs are unchanged.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph Equiv
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (a : H.RimDart (numberedWheelCycles oddWheelCycle)) (hi : OddRimIndependentOnly H a)
  {K : SigmaGraph [] []} {circles : List (Fin 1889684)}
  (t : Smoothing (oddIndependentCutGraph a hi) K circles) [IsEmpty K.Joint]
  (j : WheelCycleIndex) (D : K.SimpleCircuit)
  (hl : ∀ i : Fin D.length, Port.label K.jointLabel (D.dart i) ∈ Set.range (numberedWheelCycles j).edge)

@[reducible] noncomputable def oddErasureRecoveredCircuit : H.SimpleCircuit :=
  D.mapAlong (oddIndependentErasurePorts a hi t) (oddIndependentErasurePorts_vertex a hi t)
    (fun i => (oddIndependentErasurePorts_twin a hi t j (D.dart i) (hl i)).symm)

theorem oddErasureRecoveredCircuit_port (x : Fin D.length × Bool) :
    (oddErasureRecoveredCircuit a hi t j D hl).port x = oddIndependentErasurePorts a hi t (D.port x) :=
  D.mapAlong_port _ _ _ x

theorem oddErasureRecoveredCircuit_label (i : Fin D.length) :
    Port.label H.jointLabel ((oddErasureRecoveredCircuit a hi t j D hl).dart i) =
      Port.label K.jointLabel (D.dart i) := oddIndependentErasurePorts_label a hi t (D.dart i)

theorem oddErasureRecoveredCircuit_rim (i : Fin D.length) :
    Port.label H.jointLabel ((oddErasureRecoveredCircuit a hi t j D hl).dart i) ∈
      Set.range (numberedWheelCycles j).edge := by
  rw [oddErasureRecoveredCircuit_label]
  exact hl i

theorem oddErasureRecoveredCircuit_face (side : Bool)
    (hf : (oddErasureRecoveredCircuit a hi t j D hl).BoundsFaceOrbit side) : D.BoundsFaceOrbit side := by
  apply D.boundsFaceOrbit_of_corner_rotation side
  intro i
  apply (oddIndependentErasurePorts a hi t).injective
  rw [oddIndependentErasurePorts_rotation]
  have hr := (oddErasureRecoveredCircuit a hi t j D hl).corner_rotation_of_boundsFaceOrbit side hf i
  rw [oddErasureRecoveredCircuit_port, oddErasureRecoveredCircuit_port] at hr
  exact hr

theorem oddErasureRecoveredCircuit_cover
    (hc : (oddErasureRecoveredCircuit a hi t j D hl).IsLabelCover) : D.IsLabelCover := by
  intro i
  let e := oddIndependentErasurePorts a hi t
  obtain ⟨p, hp⟩ := D.port_eq_hubAt i false
  change D.dart i = .hub (D.hubAt i) p at hp
  obtain ⟨q, hq⟩ := D.port_eq_hubAt (finRotate D.length i) true
  change K.pairing.twin (D.dart ((finRotate D.length).symm (finRotate D.length i))) =
    .hub (D.hubAt (finRotate D.length i)) q at hq
  rw [Equiv.symm_apply_apply] at hq
  obtain ⟨g, m, hg, hgl, _⟩ := oddIndependentErasurePorts_hub a hi t (D.hubAt i) p
  obtain ⟨g', n, hg', hgl', _⟩ := oddIndependentErasurePorts_hub a hi t (D.hubAt (finRotate D.length i)) q
  have hx : e (D.dart i) = .hub g m := (congrArg e hp).trans hg
  have hy : H.pairing.twin (e (D.dart i)) = .hub g' n :=
    (oddIndependentErasurePorts_twin a hi t j (D.dart i) (hl i)).symm.trans ((congrArg e hq).trans hg')
  obtain ⟨u, v, _, _, hu, hv, _, hne⟩ := hc i
  have hgu : g = u := (H.row_hub_eq_iff.mp (hx.symm.trans hu)).1
  have hgv : g' = v := (H.row_hub_eq_iff.mp (hy.symm.trans hv)).1
  have hlabels : K.hubLabel (D.hubAt i) ≠ K.hubLabel (D.hubAt (finRotate D.length i)) := by
    intro he
    apply hne
    exact (congrArg H.hubLabel hgu).symm.trans
      (hgl.trans (he.trans (hgl'.symm.trans (congrArg H.hubLabel hgv))))
  exact ⟨D.hubAt i, D.hubAt (finRotate D.length i), p, q, hp, hq,
    fun he => hlabels (congrArg K.hubLabel he), hlabels⟩

end ThomGame.Construction
