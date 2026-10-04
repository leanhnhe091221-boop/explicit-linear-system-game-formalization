module

public import ThomGame.Pictures.CircuitEmptyCorners

/-!
# A common empty side along an actual rim path joins its cut edges in a face

The path data list incoming and outgoing actual darts, their distinct
corners, and the original edge pairings. A common frontier side forces
one of the two possible pairs of endpoint darts to share an actual face.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

structure MarkedPath where
  length : Nat
  entry : Fin (length + 1) → G.Dart
  exit : Fin length → G.Dart
  terminal : G.Dart
  entry_marked : ∀ i, C.Marked (entry i)
  exit_marked : ∀ i, C.Marked (exit i)
  terminal_marked : C.Marked terminal
  corner_vertex : ∀ i, (exit i).vertex = (entry i.castSucc).vertex
  corner_ne : ∀ i, exit i ≠ entry i.castSucc
  cross : ∀ i, G.pairing.twin (exit i) = entry i.succ
  terminal_vertex : terminal.vertex = (entry (Fin.last length)).vertex
  terminal_ne : terminal ≠ entry (Fin.last length)

namespace MarkedPath

variable {C} (p : C.MarkedPath)

theorem entry_sector {b : Bool} (hb : C.Sector b (p.entry 0)) (i : Fin (p.length + 1)) :
    C.Sector b (p.entry i) := by
  induction i using Fin.induction with
  | zero => exact hb
  | succ i ih =>
    have he := C.sector_other_marked (p.entry_marked i.castSucc) (p.exit_marked i)
      (p.corner_vertex i).symm (p.corner_ne i).symm ih
    have ht := C.sector_twin_of_marked (p.exit_marked i) he
    simpa only [Bool.not_not, p.cross i] using ht

theorem terminal_sector {b : Bool} (hb : C.Sector b (p.entry 0)) : C.Sector (!b) p.terminal :=
  C.sector_other_marked (p.entry_marked (Fin.last p.length)) p.terminal_marked
    p.terminal_vertex.symm p.terminal_ne.symm (p.entry_sector hb _)

variable (s : Bool)
  (hext : ∀ i, ∀ z : G.Dart, z.vertex = (p.entry i).vertex → ¬ C.Marked z → C.Frontier s z)

include hext in
theorem entry_same_face (i : Fin (p.length + 1)) :
    G.circuitStep.SameCycle (C.sidePort (!s) (p.entry 0)) (C.sidePort (!s) (p.entry i)) := by
  induction i using Fin.induction with
  | zero => exact Perm.SameCycle.rfl
  | succ i ih =>
    have hc := C.empty_corner_sameCycle s (p.entry_marked i.castSucc) (p.exit_marked i)
      (p.corner_vertex i).symm (hext i.castSucc)
    have hp : C.sidePort (!s) (p.exit i) = C.sidePort (!s) (p.entry i.succ) :=
      (C.sidePort_twin (!s) (p.exit_marked i)).symm.trans (congrArg (C.sidePort (!s)) (p.cross i))
    rw [hp] at hc
    exact ih.trans hc

include hext in
theorem terminal_same_face :
    G.circuitStep.SameCycle (C.sidePort (!s) (p.entry 0)) (C.sidePort (!s) p.terminal) :=
  (p.entry_same_face s hext (Fin.last p.length)).trans
    (C.empty_corner_sameCycle s (p.entry_marked (Fin.last p.length)) p.terminal_marked
      p.terminal_vertex.symm (hext (Fin.last p.length)))

include hext in
theorem forward_corner_rotation (hb : C.Sector s (p.entry 0)) (i : Fin p.length) :
    G.rotation (p.entry i.castSucc) = p.exit i :=
  C.empty_corner_rotation_of_sector (p.entry_marked i.castSucc) (p.exit_marked i)
    (p.corner_vertex i).symm (p.corner_ne i).symm (p.entry_sector hb _) (hext i.castSucc)

include hext in
theorem forward_terminal_rotation (hb : C.Sector s (p.entry 0)) :
    G.rotation (p.entry (Fin.last p.length)) = p.terminal :=
  C.empty_corner_rotation_of_sector (p.entry_marked _) p.terminal_marked
    p.terminal_vertex.symm p.terminal_ne.symm (p.entry_sector hb _) (hext _)

include hext in
theorem backward_corner_rotation (hb : C.Sector (!s) (p.entry 0)) (i : Fin p.length) :
    G.rotation (p.exit i) = p.entry i.castSucc := by
  have hs := C.sector_other_marked (p.entry_marked i.castSucc) (p.exit_marked i)
    (p.corner_vertex i).symm (p.corner_ne i).symm (p.entry_sector hb _)
  simp only [Bool.not_not] at hs
  exact C.empty_corner_rotation_of_sector (p.exit_marked i) (p.entry_marked i.castSucc)
    (p.corner_vertex i) (p.corner_ne i) hs
    (fun z hz hn => hext i.castSucc z (hz.trans (p.corner_vertex i)) hn)

include hext in
theorem backward_terminal_rotation (hb : C.Sector (!s) (p.entry 0)) :
    G.rotation p.terminal = p.entry (Fin.last p.length) := by
  have hs := p.terminal_sector hb
  simp only [Bool.not_not] at hs
  exact C.empty_corner_rotation_of_sector p.terminal_marked (p.entry_marked _)
    p.terminal_vertex p.terminal_ne hs
    (fun z hz hn => hext _ z (hz.trans p.terminal_vertex) hn)

include hext in
theorem exists_face_orientation_and_corners : ∃ o : Bool,
    G.circuitStep.SameCycle (if o then p.entry 0 else p.terminal)
      (G.pairing.twin (if o then p.terminal else p.entry 0)) ∧
    (∀ i, G.rotation (if o then p.exit i else p.entry i.castSucc) =
      (if o then p.entry i.castSucc else p.exit i)) ∧
    G.rotation (if o then p.terminal else p.entry (Fin.last p.length)) =
      (if o then p.entry (Fin.last p.length) else p.terminal) := by
  obtain ⟨b, hb⟩ := C.sector_exists_of_marked (p.entry_marked 0)
  have ht := p.terminal_sector hb
  have hf := p.terminal_same_face s hext
  by_cases hbs : b = s
  · subst b
    have hb' : C.Sector (!(!s)) (p.entry 0) := by simpa only [Bool.not_not] using hb
    rw [C.sidePort_of_opposite hb', C.sidePort_of_sector ht] at hf
    exact ⟨false, hf.symm, p.forward_corner_rotation s hext hb,
      p.forward_terminal_rotation s hext hb⟩
  · have he : b = !s := by cases b <;> cases s <;> simp_all
    subst b
    rw [C.sidePort_of_sector hb, C.sidePort_of_opposite ht] at hf
    exact ⟨true, hf, p.backward_corner_rotation s hext hb,
      p.backward_terminal_rotation s hext hb⟩

include hext in
theorem exists_face_orientation : ∃ o : Bool,
    G.circuitStep.SameCycle (if o then p.entry 0 else p.terminal)
      (G.pairing.twin (if o then p.terminal else p.entry 0)) := by
  obtain ⟨o, ho, _⟩ := p.exists_face_orientation_and_corners s hext
  exact ⟨o, ho⟩

end MarkedPath
end ThomGame.Pictures.PortGraph.SimpleCircuit
