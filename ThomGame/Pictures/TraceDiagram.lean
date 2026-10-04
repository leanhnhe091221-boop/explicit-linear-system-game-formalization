module

public import ThomGame.Pictures.Diagram

/-!
# Compiling finite local derivations into diagram syntax

Every elementary step is realized by a cap, cup, or relation vertex between
unchanged identity wires. The compilation preserves the exact list of
relation occurrences, not only its parity. Thus the diagram calculus is
both sound and complete for the actual presented-group word equations.
-/

@[expose] public section
namespace ThomGame.Pictures

open InvolutionDerivation

variable {R S : Type*} (P : InvolutionPresentation R S)

def moveDiagram : (m : Move R S) → Diagram P (m.source P).1.toList (m.target P).1.toList
  | .eraseSquare l r s _ =>
      (Diagram.cap s).contextDown l r
  | .insertSquare l r s _ =>
      (Diagram.cup s).contextUp l r
  | .eraseRelation l r i _ =>
      (Diagram.down i).contextDown l r
  | .insertRelation l r i _ =>
      (Diagram.up i).contextUp l r

theorem labels_moveDiagram (m : Move R S) :
    (moveDiagram P m).labels = m.label.toList := by
  cases m with
  | eraseSquare l r s a => exact Diagram.labels_contextDown (Diagram.cap s) l r
  | insertSquare l r s a => exact Diagram.labels_contextUp (Diagram.cup s) l r
  | eraseRelation l r i a => exact Diagram.labels_contextDown (Diagram.down i) l r
  | insertRelation l r i a => exact Diagram.labels_contextUp (Diagram.up i) l r

theorem sign_moveDiagram (m : Move R S) : (moveDiagram P m).sign = m.parity P := by
  simp only [Diagram.sign, labels_moveDiagram]
  cases m <;> simp [Move.label, Move.parity]

theorem diagram_of_valid {ms : List (Move R S)} {u v : State S} (h : Valid P ms u v) :
    ∃ d : Diagram P u.1.toList v.1.toList, d.labels = relationUses ms := by
  induction ms generalizing u with
  | nil =>
    change u = v at h
    subst v
    exact ⟨.identity u.1.toList, rfl⟩
  | cons m ms ih =>
    rcases h with ⟨rfl, h⟩
    obtain ⟨d, hd⟩ := ih h
    refine ⟨(moveDiagram P m).comp d, ?_⟩
    rw [Diagram.labels, labels_moveDiagram, hd]
    cases m <;> rfl

theorem word_eq_iff_diagram (w : List S) (a : ZMod 2) :
    (w.map (InvolutionPresentation.x P)).prod = (if a = 1 then InvolutionPresentation.J P else 1) ↔
      ∃ d : Diagram P w [], d.sign = a := by
  constructor
  · intro h
    obtain ⟨ms, hms⟩ := (word_eq_iff_trace P w a).mp h
    obtain ⟨d, hd⟩ := diagram_of_valid P hms
    refine ⟨d, ?_⟩
    change (d.labels.map P.parity).sum = a
    rw [hd, ← sign_eq_relation_sum]
    exact valid_word_sign P hms
  · rintro ⟨d, hd⟩
    have h := d.boundary_eq
    simpa only [List.map_nil, List.prod_nil, one_mul, hd] using h

theorem J_eq_one_iff_closed_odd_diagram :
    InvolutionPresentation.J P = 1 ↔ ∃ d : Diagram P [] [], d.sign = 1 := by
  have h := word_eq_iff_diagram P [] 1
  change (1 : InvolutionPresentation.GroupOf P) = InvolutionPresentation.J P ↔
    ∃ d : Diagram P [] [], d.sign = 1 at h
  exact eq_comm.trans h

end ThomGame.Pictures
