module

public import ThomGame.Pictures.BoundaryQuadPath
public import ThomGame.Pictures.OpenGraphBlocks

/-!
# A boundary quadrilateral closes to exactly one capped face orbit

The face walk runs from start to finish along three graph edges. The
specified boundary successor runs from start to finish too, so capping
by its inverse closes the walk. The resulting face orbit contains
exactly those three darts. This establishes the combinatorial facial
statement; placement of disconnected components in a geometric disk
is not part of this result.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.BoundaryQuadPath

open Equiv CyclicBlock
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (q : G.BoundaryQuadPath)

theorem capped_first_step :
    (G.cappedRotation * G.pairing.perm) q.firstDart = q.middleDart := by
  change G.cappingTargets (G.circuitStep q.firstDart) = q.middleDart
  rw [q.first_step]
  exact G.cappingTargets_unmarked _ (fun h => h)

theorem capped_second_step :
    (G.cappedRotation * G.pairing.perm) q.middleDart = q.lastDart := by
  change G.cappingTargets (G.circuitStep q.middleDart) = q.lastDart
  rw [q.second_step]
  exact G.cappingTargets_unmarked _ (fun h => h)

theorem capped_last_step :
    (G.cappedRotation * G.pairing.perm) q.lastDart = q.firstDart := by
  change G.cappingTargets (G.circuitStep q.lastDart) = q.firstDart
  rw [q.last_step, G.cappingTargets_boundary, ← q.boundary_adjacent, Equiv.symm_apply_apply]

theorem capped_face_word :
    IsCycleWord (G.cappedRotation * G.pairing.perm) [q.firstDart, q.middleDart, q.lastDart] := by
  have hfm : q.firstDart ≠ q.middleDart :=
    fun he => q.first_edge_ne_middle (congrArg G.pairing.edge he)
  have hfl : q.firstDart ≠ q.lastDart :=
    fun he => q.first_edge_ne_last (congrArg G.pairing.edge he)
  have hml : q.middleDart ≠ q.lastDart :=
    fun he => q.middle_edge_ne_last (congrArg G.pairing.edge he)
  refine ⟨by simp [hfm, hfl, hml], by simp, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [q.capped_first_step, List.formPerm_cons_cons, List.formPerm_pair, Perm.mul_apply,
      swap_apply_of_ne_of_ne hfm hfl, swap_apply_left]
  · rw [q.capped_second_step, List.formPerm_cons_cons, List.formPerm_pair, Perm.mul_apply,
      swap_apply_left, swap_apply_of_ne_of_ne hfl.symm hml.symm]
  · rw [q.capped_last_step, List.formPerm_cons_cons, List.formPerm_pair, Perm.mul_apply,
      swap_apply_right, swap_apply_right]

theorem capped_face_iff (x : G.Dart) :
    (G.cappedRotation * G.pairing.perm).SameCycle q.firstDart x ↔
      x = q.firstDart ∨ x = q.middleDart ∨ x = q.lastDart := by
  have h := q.capped_face_word.mem_iff_sameCycle (by simp : q.firstDart ∈
    [q.firstDart, q.middleDart, q.lastDart]) x
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h.symm

end ThomGame.Pictures.PortGraph.BoundaryQuadPath
