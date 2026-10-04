module

public import ThomGame.Pictures.Duality
public import Mathlib.Data.List.Permutation

/-!
# Reordering the boundary of a single triangular vertex

Cups, caps, and boundary bending implement cyclic rotation and reversal.
For three ports these realize every permutation, with exactly the same
relation-vertex multiset. No crossing generator is introduced.
-/

@[expose] public section
namespace ThomGame.Pictures.Diagram

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}

theorem labels_capWord (w : List S) : (capWord P w).labels = [] := by
  apply List.perm_nil.mp
  exact (labels_adjoint_perm (cupWord P w)).trans (by rw [labels_cupWord])

theorem labels_close {u v : List S} (d : Diagram P u v) : d.close.labels = d.labels := by
  simp [close, labels, labels_capWord]

def bendFirst {a : S} (d : Diagram P (a :: w) []) : Diagram P w [a] :=
  (((cup a).tensor (identity w)).comp ((identity [a]).tensor d)).cast (by simp) (by simp)

theorem labels_bendFirst {a : S} (d : Diagram P (a :: w) []) :
    d.bendFirst.labels = d.labels := by
  simp [bendFirst, labels_cast, labels]

def rotateDown {a : S} (d : Diagram P (a :: w) []) : Diagram P (w ++ [a]) [] :=
  d.bendFirst.close.cast (by simp) rfl

theorem labels_rotateDown {a : S} (d : Diagram P (a :: w) []) :
    d.rotateDown.labels = d.labels := by
  rw [rotateDown, labels_cast, labels_close, labels_bendFirst]

def reverseDown (d : Diagram P w []) : Diagram P w.reverse [] :=
  (((identity w.reverse).tensor d.adjoint).comp
    ((capWord P w.reverse).cast (by simp) rfl)).cast (by simp) rfl

theorem labels_reverseDown_perm (d : Diagram P w []) :
    d.reverseDown.labels.Perm d.labels := by
  simpa [reverseDown, labels_cast, labels, labels_capWord] using d.labels_adjoint_perm

/-- The six permutations of three ports are rotations of the original
order or of its reversal, even when some labels coincide. -/
theorem exists_permuted_triangle {a b c : S} (d : Diagram P [a, b, c] [])
    (hw : w.Perm [a, b, c]) :
    ∃ e : Diagram P w [], e.labels.Perm d.labels := by
  let dr : Diagram P [c, b, a] [] := d.reverseDown.cast (by simp) rfl
  have hdr : dr.labels.Perm d.labels := by
    simpa only [dr, labels_cast] using d.labels_reverseDown_perm
  have hp : [a, b, c].permutations =
      [[a, b, c], [b, a, c], [c, b, a], [b, c, a], [c, a, b], [a, c, b]] := by
    cbv
  have hm := List.mem_permutations.mpr hw
  rw [hp] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨d, .refl _⟩
  · exact ⟨dr.rotateDown, by rw [labels_rotateDown]; exact hdr⟩
  · exact ⟨dr, hdr⟩
  · exact ⟨d.rotateDown, by rw [labels_rotateDown]⟩
  · exact ⟨d.rotateDown.rotateDown, by rw [labels_rotateDown, labels_rotateDown]⟩
  · exact ⟨dr.rotateDown.rotateDown, by
      rw [labels_rotateDown, labels_rotateDown]
      exact hdr⟩

end ThomGame.Pictures.Diagram
