module

public import ThomGame.Pictures.NoncrossingPairing
public import ThomGame.Pictures.DiagramBoundaryMoves
public import Mathlib.Data.List.OfFn

/-!
# Realizing a noncrossing matching by a vertex-free diagram

The first chord separates the remaining matching into two invariant
linear intervals. Their recursively constructed diagrams are enclosed
by a cap and juxtaposed, using no crossings or relation vertices.
-/

@[expose] public section
namespace ThomGame.Pictures

open CircularPartition NoncrossingPairing

variable {R S : Type*} {P : InvolutionPresentation R S}

theorem ofFn_firstChord {n : Nat} (label : Fin (n + 1) → S) (j : Fin (n + 1)) (hj : 0 < j.val) :
    List.ofFn label = [label 0] ++
      List.ofFn (fun i => label (intervalIndex (n + 1) 1 (j.val - 1) (by omega) i).val) ++
      [label j] ++
      List.ofFn (fun i => label (intervalIndex (n + 1) (j.val + 1) (n - j.val) (by omega) i).val) := by
  have hlen : n + 1 = 1 + (j.val - 1) + 1 + (n - j.val) := by omega
  rw [List.ofFn_congr hlen]
  simp only [List.ofFn_add, List.ofFn_succ, List.ofFn_zero, List.nil_append,
    List.cons_append, List.append_assoc]
  congr 1
  congr 1
  apply congrArg₂ List.cons
  · apply congrArg label
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_castLE, Fin.val_natAdd, Fin.val_zero]
    omega
  · apply congrArg List.ofFn
    funext i
    apply congrArg label
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, intervalIndex, Equiv.coe_fn_mk]
    omega

namespace Diagram

variable {w : List S}

def enclose (d : Diagram P w []) (s : S) : Diagram P ([s] ++ w ++ [s]) [] :=
  (d.context [s] [s]).comp (cap s)

theorem labels_enclose (d : Diagram P w []) (s : S) : (d.enclose s).labels = d.labels := by
  simp [enclose, labels, labels_context]

end Diagram

/-- Every labelled noncrossing matching has a realization with no relation vertices. -/
theorem exists_matching_diagram (P : InvolutionPresentation R S) {n : Nat}
    (label : Fin n → S) (p : Pairing label) (hnc : NonInterlacing sbtw p.perm) :
    ∃ d : Diagram P (List.ofFn label) [], d.labels = [] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨.identity [], rfl⟩
    | succ n =>
      let j : Fin (n + 1) := p.twin 0
      have hj : 0 < j.val := p.first_twin_pos
      have hI : 1 + (j.val - 1) ≤ n + 1 := by omega
      have hO : j.val + 1 + (n - j.val) ≤ n + 1 := by omega
      have closedI : ∀ i : Fin (n + 1), 1 ≤ i.val ∧ i.val < 1 + (j.val - 1) →
          1 ≤ (p.twin i).val ∧ (p.twin i).val < 1 + (j.val - 1) := by
        intro i hi
        have hx := p.firstChord_inside_stable hnc i (by change 0 < i.val ∧ i.val < j.val; omega)
        change 0 < (p.twin i).val ∧ (p.twin i).val < j.val at hx
        omega
      have closedO : ∀ i : Fin (n + 1), j.val + 1 ≤ i.val ∧ i.val < j.val + 1 + (n - j.val) →
          j.val + 1 ≤ (p.twin i).val ∧ (p.twin i).val < j.val + 1 + (n - j.val) := by
        intro i hi
        have hx := p.firstChord_after_stable hnc i (by change j.val < i.val; omega)
        change j.val < (p.twin i).val at hx
        omega
      let labelI := fun i => label (intervalIndex (n + 1) 1 (j.val - 1) hI i).val
      let labelO := fun i => label (intervalIndex (n + 1) (j.val + 1) (n - j.val) hO i).val
      let pI := interval p 1 (j.val - 1) hI closedI
      let pO := interval p (j.val + 1) (n - j.val) hO closedO
      obtain ⟨dI, hdI⟩ := ih (j.val - 1) (by omega) labelI pI
        (interval_noninterlacing p hnc 1 (j.val - 1) hI closedI)
      obtain ⟨dO, hdO⟩ := ih (n - j.val) (by omega) labelO pO
        (interval_noninterlacing p hnc (j.val + 1) (n - j.val) hO closedO)
      have hl : label j = label 0 := p.label_twin 0
      have hw : List.ofFn label = [label 0] ++ List.ofFn labelI ++ [label 0] ++ List.ofFn labelO := by
        exact (ofFn_firstChord label j hj).trans (by rw [hl])
      refine ⟨((dI.enclose (label 0)).tensor dO).cast hw.symm rfl, ?_⟩
      exact (Diagram.labels_cast _ _ _).trans (by
        simp only [Diagram.labels, Diagram.labels_enclose, hdI, hdO, List.nil_append])

theorem exists_matching_word_diagram (P : InvolutionPresentation R S) (w : List S)
    (p : Pairing (fun i : Fin w.length => w[i])) (hnc : NonInterlacing sbtw p.perm) :
    ∃ d : Diagram P w [], d.labels = [] := by
  obtain ⟨d, hd⟩ := exists_matching_diagram P (fun i : Fin w.length => w[i]) p hnc
  exact ⟨d.cast (by simp) rfl, (Diagram.labels_cast _ _ _).trans hd⟩

end ThomGame.Pictures
