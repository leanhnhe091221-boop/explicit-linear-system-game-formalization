module

public import ThomGame.Pictures.SunSwitchInvolution
public import ThomGame.Pictures.SunComponentSpokes
public import ThomGame.Pictures.SunSplitSpokeCount

/-!
# Actual spoke-edge counts when two distinct rims join

The inverse switch splits the joined rim. Its proved edge partition,
the exact involutivity of the switch, and the partition of ambient
component edges into two sides give the join formula. It is first stated
additively, so the subtraction form does not conceal truncation at zero.
Global outer-side choices and disconnected-component placement are not
assumed or inferred from this local formula.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right)
  (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))

include hEuler hf hc in
theorem join_spoke_side_count :
    s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!s.switch.hubFlip s.left) =
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (G.hubFlip s.left) +
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) (G.hubFlip s.right) + 1 := by
  have hnewEuler := s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler))
  have hnewFlip : s.switch.hubFlip s.left = s.switch.hubFlip s.right := by
    rw [s.switch_flip_left, s.switch_flip_right, hf]
  have hcount := s.switchedSpoke.split_spoke_count hn hu hv hnewEuler hnewFlip
    (s.switch_rim_joins hn hu hv hc)
  change s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!s.switch.hubFlip s.left) =
    s.switchedSpoke.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true)
      (s.switchedSpoke.switch.hubFlip s.left) +
    s.switchedSpoke.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true)
      (s.switchedSpoke.switch.hubFlip s.right) + 1 at hcount
  have hleft := (s.switch_twice_sideSpokeCount hn hu hv (G.sunRimPort hn s.left true)
    (s.switchedSpoke.switch.hubFlip s.left)).trans
      (congrArg (fun side => G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) side)
        (s.switch_twice_flip s.left))
  have hright := (s.switch_twice_sideSpokeCount hn hu hv (G.sunRimPort hn s.right true)
    (s.switchedSpoke.switch.hubFlip s.right)).trans
      (congrArg (fun side => G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) side)
        (s.switch_twice_flip s.right))
  exact hcount.trans (congrArg₂ (fun l r => l + r + 1) hleft hright)

include hEuler hf hc in
/-- The original left spoke side consists, in cardinality, of the new
opposite side, the old right opposite side, and the selected spoke. -/
theorem join_spoke_count_add :
    G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left) =
      s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) +
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) (G.hubFlip s.right) + 1 := by
  have hold := G.sunComponentSpokeCount_eq_sides hn hu hv
    (G.dualEuler_eq_twice_components hEuler) (G.sunRimPort hn s.left true) (G.hubFlip s.left)
  have hnew := s.switch.sunComponentSpokeCount_eq_sides hn hu hv
    (s.switch_dualEuler hEuler hf) (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left)
  have htotal := s.switch_component_spoke_count hn (G.sunRimPort hn s.left true)
  have hjoin := s.join_spoke_side_count hn hu hv hEuler hf hc
  omega

include hEuler hf hc in
theorem join_spoke_count :
    s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) =
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left) -
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) (G.hubFlip s.right) - 1 := by
  have h := s.join_spoke_count_add hn hu hv hEuler hf hc
  omega

include hEuler hf hc in
theorem join_spoke_count_lt :
    s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) <
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left) := by
  have h := s.join_spoke_count_add hn hu hv hEuler hf hc
  omega

end ThomGame.Pictures.PortGraph.SunSpoke

namespace ThomGame.Pictures.PortGraph.SunMinimalState

open RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState)
  (s : G.SunSpoke) (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include h in
theorem join_spoke_count
    (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn (by simp) hw).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    s.switch.sunSideSpokeCount hn (by simp) hw (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) =
      G.sunSideSpokeCount hn (by simp) hw (G.sunRimPort hn s.left true) (!G.hubFlip s.left) -
      G.sunSideSpokeCount hn (by simp) hw (G.sunRimPort hn s.right true) (G.hubFlip s.right) - 1 :=
  s.join_spoke_count hn (by simp) hw h.euler (h.same_flip s) hc

end ThomGame.Pictures.PortGraph.SunMinimalState
