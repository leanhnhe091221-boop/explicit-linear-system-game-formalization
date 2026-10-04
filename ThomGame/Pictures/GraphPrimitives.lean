module

public import ThomGame.Pictures.GraphComposition

/-! # Finite port graphs for the five primitive diagram constructors -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} (P : InvolutionPresentation R S)

def identity (w : List S) : PortGraph P w w where
  Hub := Empty
  Joint := Empty
  hubLabel := Empty.elim
  hubFlip := Empty.elim
  jointLabel := Empty.elim
  pairing := {
    twin := fun
      | .top i => .bottom i
      | .bottom i => .top i
      | .hub h _ => nomatch h
      | .joint j _ => nomatch j
    involutive := by intro a; cases a <;> first | rfl | contradiction
    ne_self := by
      intro a
      cases a with
      | top i => simp
      | bottom i => simp
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim
    label_twin := by intro a; cases a <;> first | rfl | contradiction }

def cap (s : S) : PortGraph P [s, s] [] where
  Hub := Empty
  Joint := Empty
  hubLabel := Empty.elim
  hubFlip := Empty.elim
  jointLabel := Empty.elim
  pairing := {
    twin := fun
      | .top i => .top i.rev
      | .bottom i => Fin.elim0 i
      | .hub h _ => nomatch h
      | .joint j _ => nomatch j
    involutive := by
      intro a
      cases a with
      | top i => exact congrArg Port.top (Fin.rev_rev i)
      | bottom i => exact Fin.elim0 i
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim
    ne_self := by
      intro a
      cases a with
      | top i =>
        intro h
        exact (by decide +kernel : ∀ k : Fin 2, k.rev ≠ k) i (Port.top.inj h)
      | bottom i => exact Fin.elim0 i
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim
    label_twin := by
      intro a
      cases a with
      | top i => fin_cases i <;> rfl
      | bottom i => exact Fin.elim0 i
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim }

def cup (s : S) : PortGraph P [] [s, s] where
  Hub := Empty
  Joint := Empty
  hubLabel := Empty.elim
  hubFlip := Empty.elim
  jointLabel := Empty.elim
  pairing := {
    twin := fun
      | .top i => Fin.elim0 i
      | .bottom i => .bottom i.rev
      | .hub h _ => nomatch h
      | .joint j _ => nomatch j
    involutive := by
      intro a
      cases a with
      | top i => exact Fin.elim0 i
      | bottom i => exact congrArg Port.bottom (Fin.rev_rev i)
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim
    ne_self := by
      intro a
      cases a with
      | top i => exact Fin.elim0 i
      | bottom i =>
        intro h
        exact (by decide +kernel : ∀ k : Fin 2, k.rev ≠ k) i (Port.bottom.inj h)
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim
    label_twin := by
      intro a
      cases a with
      | top i => exact Fin.elim0 i
      | bottom i => fin_cases i <;> rfl
      | hub h _ => exact h.elim
      | joint j _ => exact j.elim }

def down (r : R) : PortGraph P (P.word r) [] where
  Hub := Unit
  Joint := Empty
  hubLabel := fun _ => r
  hubFlip := fun _ => false
  jointLabel := Empty.elim
  pairing := {
    twin := fun
      | .top i => .hub () i
      | .bottom i => Fin.elim0 i
      | .hub _ i => .top i
      | .joint j _ => nomatch j
    involutive := by
      intro a
      cases a with
      | top i => rfl
      | bottom i => exact Fin.elim0 i
      | hub h i => cases h; rfl
      | joint j _ => exact j.elim
    ne_self := by
      intro a
      cases a with
      | top i => simp
      | bottom i => exact Fin.elim0 i
      | hub h i => simp
      | joint j _ => exact j.elim
    label_twin := by
      intro a
      cases a with
      | top i => rfl
      | bottom i => exact Fin.elim0 i
      | hub h i => rfl
      | joint j _ => exact j.elim }

def up (r : R) : PortGraph P [] (P.word r) where
  Hub := Unit
  Joint := Empty
  hubLabel := fun _ => r
  hubFlip := fun _ => true
  jointLabel := Empty.elim
  pairing := {
    twin := fun
      | .top i => Fin.elim0 i
      | .bottom i => .hub () i
      | .hub _ i => .bottom i
      | .joint j _ => nomatch j
    involutive := by
      intro a
      cases a with
      | top i => exact Fin.elim0 i
      | bottom i => rfl
      | hub h i => cases h; rfl
      | joint j _ => exact j.elim
    ne_self := by
      intro a
      cases a with
      | top i => exact Fin.elim0 i
      | bottom i => simp
      | hub h i => simp
      | joint j _ => exact j.elim
    label_twin := by
      intro a
      cases a with
      | top i => exact Fin.elim0 i
      | bottom i => rfl
      | hub h i => rfl
      | joint j _ => exact j.elim }

end ThomGame.Pictures.PortGraph
