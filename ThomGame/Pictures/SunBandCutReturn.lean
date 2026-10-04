module

public import ThomGame.Pictures.SunBandCutGraph
public import ThomGame.Pictures.SlotErasureEuler
public import ThomGame.Pictures.CappedGraphRealization

/-!
# First-return rotation after cutting a three-label sun circuit

At each selected triangle, deleting its fixed rim slot leaves the
two-cycle between its spoke and unused rim slot. This is checked for
both cyclic orientations. All other vertices retain their rotations.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

theorem sunBandCutReturn_joint (r : Perm G.Dart)
    (hr : ∀ (h : G.Hub) (p : Fin 3), r (.hub h p) = G.rotation (.hub h p))
    (k : Fin C.length) (side : Bool) :
    (MarkedReturn.perm r C.SunBandCutKeep (C.sunBandCutPorts hn i hband (.joint k side))).val =
      C.sunBandCutPort i (.joint k (!side)) := by
  have hslot : C.sunBandExternalSlot i k = 1 ∨ C.sunBandExternalSlot i k = 2 := by
    have hne := C.sunBandExternalSlot_ne_zero i k
    have hb := (C.sunBandExternalSlot i k).isLt
    omega
  have hstep :
      r (C.sunBandCutPort i (.joint k side)) = C.sunBandCutPort i (.joint k (!side)) ∨
      (¬ C.SunBandCutKeep (r (C.sunBandCutPort i (.joint k side))) ∧
        r (r (C.sunBandCutPort i (.joint k side))) = C.sunBandCutPort i (.joint k (!side))) := by
    have hm1 : (-1 : Fin 3) = 2 := by decide +kernel
    rcases hslot with hs | hs <;> cases side <;> cases hf : G.hubFlip (C.hubAt k)
    all_goals simp [sunBandCutPort, sunBandSpokePort, sunBandExternalPort, hr,
      G.sun_rotation_hub, hf, hs, C.sunBandCutKeep_hubAt_iff hn i hband k,
      finRotate_apply, finRotate_symm_apply, hm1]
  rcases hstep with he | ⟨hm, he⟩
  · exact (MarkedReturn.perm_val_of_step r C.SunBandCutKeep
      (C.sunBandCutPorts hn i hband (.joint k side))
      (he ▸ C.sunBandCutPort_kept hn i hband (.joint k (!side)))).trans he
  · exact (MarkedReturn.perm_val_of_two_steps r C.SunBandCutKeep
      (C.sunBandCutPorts hn i hband (.joint k side)) hm
      (he ▸ C.sunBandCutPort_kept hn i hband (.joint k (!side)))).trans he

variable {w : List (Fin n ⊕ Fin n)} {B : PortGraph (sunPresentation n b) w []}
  [IsEmpty B.Joint] (D : B.SimpleCircuit)
  (hD : ∀ k : Fin D.length, SunBandLabel i (Port.label B.jointLabel (D.dart k)))

theorem sunBandCutGraph_cappedRotation (x : (D.sunBandCutGraph hn i hD).Dart) :
    MarkedReturn.perm B.cappedRotation D.SunBandCutKeep (D.sunBandCutPorts hn i hD x) =
      D.sunBandCutPorts hn i hD ((D.sunBandCutGraph hn i hD).cappedRotation x) := by
  apply Subtype.ext
  cases x with
  | top j =>
    have he : B.cappedRotation (D.sunBandCutPort i (.top j)) =
        D.sunBandCutPort i ((D.sunBandCutGraph hn i hD).cappedRotation (.top j)) := by
      rw [(D.sunBandCutGraph hn i hD).cappedRotation_top]
      exact B.cappedRotation_top j
    exact (MarkedReturn.perm_val_of_step B.cappedRotation D.SunBandCutKeep
      (D.sunBandCutPorts hn i hD (.top j))
      (he ▸ D.sunBandCutPort_kept hn i hD _)).trans he
  | bottom j => exact j.elim0
  | hub h p =>
    have he : B.cappedRotation (D.sunBandCutPort i (.hub h p)) =
        D.sunBandCutPort i ((D.sunBandCutGraph hn i hD).cappedRotation (.hub h p)) := by
      rw [(D.sunBandCutGraph hn i hD).cappedRotation_hub]
      exact B.cappedRotation_hub h.val p
    exact (MarkedReturn.perm_val_of_step B.cappedRotation D.SunBandCutKeep
      (D.sunBandCutPorts hn i hD (.hub h p))
      (he ▸ D.sunBandCutPort_kept hn i hD _)).trans he
  | joint k side =>
    rw [(D.sunBandCutGraph hn i hD).cappedRotation_joint]
    exact D.sunBandCutReturn_joint hn i hD B.cappedRotation B.cappedRotation_hub k side

end ThomGame.Pictures.PortGraph.SimpleCircuit
