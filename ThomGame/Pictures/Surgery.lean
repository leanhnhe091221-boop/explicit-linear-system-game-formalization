module

public import ThomGame.Pictures.Diagram

/-!
# Replacement and minimality for a specified diagram subexpression

A frame records the entire surrounding diagram and exactly one typed hole.
Replacing the hole by a diagram with the same two boundaries and sign
preserves the outer sign. Size is additive, so a minimum-size outer diagram
has a minimum-size filling at every such hole. Arbitrary geometric disk
regions have not yet been identified with these syntactic frames.
-/

@[expose] public section
namespace ThomGame.Pictures

universe uR uS
variable {R : Type uR} {S : Type uS} (P : InvolutionPresentation R S)

inductive Frame (a b : List S) : List S → List S → Type (max uR uS)
  | hole : Frame a b a b
  | pre {u v w : List S} (d : Diagram P u v) (c : Frame a b v w) : Frame a b u w
  | post {u v w : List S} (c : Frame a b u v) (d : Diagram P v w) : Frame a b u w
  | left {u v w z : List S} (d : Diagram P u v) (c : Frame a b w z) :
      Frame a b (u ++ w) (v ++ z)
  | right {u v w z : List S} (c : Frame a b u v) (d : Diagram P w z) :
      Frame a b (u ++ w) (v ++ z)

namespace Frame

variable {P} {a b u v : List S}

def fill : {u v : List S} → Frame P a b u v → Diagram P a b → Diagram P u v
  | _, _, .hole, d => d
  | _, _, .pre e c, d => e.comp (c.fill d)
  | _, _, .post c e, d => (c.fill d).comp e
  | _, _, .left e c, d => e.tensor (c.fill d)
  | _, _, .right c e, d => (c.fill d).tensor e

def size : {u v : List S} → Frame P a b u v → Nat
  | _, _, .hole => 0
  | _, _, .pre d c => d.size + c.size
  | _, _, .post c d => c.size + d.size
  | _, _, .left d c => d.size + c.size
  | _, _, .right c d => c.size + d.size

def sign : {u v : List S} → Frame P a b u v → ZMod 2
  | _, _, .hole => 0
  | _, _, .pre d c => d.sign + c.sign
  | _, _, .post c d => c.sign + d.sign
  | _, _, .left d c => d.sign + c.sign
  | _, _, .right c d => c.sign + d.sign

theorem size_fill (c : Frame P a b u v) (d : Diagram P a b) :
    (c.fill d).size = c.size + d.size := by
  induction c with
  | hole => simp [fill, size]
  | pre e c ih => simp [fill, size, Diagram.size_comp, ih, Nat.add_assoc]
  | post c e ih => simp [fill, size, Diagram.size_comp, ih, Nat.add_comm, Nat.add_left_comm]
  | left e c ih => simp [fill, size, Diagram.size_tensor, ih, Nat.add_assoc]
  | right c e ih => simp [fill, size, Diagram.size_tensor, ih, Nat.add_comm, Nat.add_left_comm]

theorem sign_fill (c : Frame P a b u v) (d : Diagram P a b) :
    (c.fill d).sign = c.sign + d.sign := by
  induction c with
  | hole => simp [fill, sign]
  | pre e c ih => simp [fill, sign, Diagram.sign_comp, ih, add_assoc]
  | post c e ih => simp [fill, sign, Diagram.sign_comp, ih, add_comm, add_left_comm]
  | left e c ih => simp [fill, sign, Diagram.sign_tensor, ih, add_assoc]
  | right c e ih => simp [fill, sign, Diagram.sign_tensor, ih, add_comm, add_left_comm]

theorem replace_sign (c : Frame P a b u v) (d e : Diagram P a b) (h : d.sign = e.sign) :
    (c.fill d).sign = (c.fill e).sign := by rw [sign_fill, sign_fill, h]

theorem replace_size_lt (c : Frame P a b u v) (d e : Diagram P a b) (h : d.size < e.size) :
    (c.fill d).size < (c.fill e).size := by
  rw [size_fill, size_fill]
  exact Nat.add_lt_add_left h c.size

end Frame

namespace Diagram

variable {P} {u v : List S}

def Minimal (d : Diagram P u v) : Prop :=
  ∀ e : Diagram P u v, e.sign = d.sign → d.size ≤ e.size

theorem exists_minimal (d : Diagram P u v) :
    ∃ e : Diagram P u v, e.sign = d.sign ∧ e.Minimal := by
  classical
  have h : ∃ n : Nat, ∃ e : Diagram P u v, e.sign = d.sign ∧ e.size = n :=
    ⟨d.size, d, rfl, rfl⟩
  obtain ⟨e, he, hn⟩ := Nat.find_spec h
  refine ⟨e, he, ?_⟩
  intro f hf
  rw [hn]
  exact Nat.find_min' h ⟨f, hf.trans he, rfl⟩

theorem minimal_filling {a b : List S} (c : Frame P a b u v) (d : Diagram P a b)
    (h : (c.fill d).Minimal) : d.Minimal := by
  intro e he
  have hh := h (c.fill e) (c.replace_sign e d he)
  rw [Frame.size_fill, Frame.size_fill] at hh
  exact Nat.le_of_add_le_add_left hh

end Diagram
end ThomGame.Pictures
