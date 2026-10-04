module

public import ThomGame.Pictures.DiagramBoundaryMoves

/-!
# Gluing ordered relation blocks along selected boundary ports

Cyclic shifts expose any selected boundary occurrence. Two exposed ports
with equal labels can then be joined by cups and composition. The two
selected occurrences disappear from the boundary, while the relation-use
lists concatenate exactly. No crossing or commutation rule is introduced.
-/

@[expose] public section
namespace ThomGame.Pictures.Diagram

variable {R S : Type*} {P : InvolutionPresentation R S}

def rotatePrefix : (l r : List S) → Diagram P (l ++ r) [] → Diagram P (r ++ l) []
  | [], r, d => d.cast (by simp) rfl
  | s :: l, r, d =>
    (rotatePrefix l (r ++ [s]) (d.rotateDown.cast (by simp [List.append_assoc]) rfl)).cast
      (by simp [List.append_assoc]) rfl

theorem labels_rotatePrefix (l r : List S) (d : Diagram P (l ++ r) []) :
    (rotatePrefix l r d).labels = d.labels := by
  induction l generalizing r with
  | nil => exact labels_cast _ _ _
  | cons s l ih =>
    exact (labels_cast _ _ _).trans ((ih _ _).trans
      ((labels_cast _ _ _).trans (labels_rotateDown d)))

def exposePort {l r : List S} {s : S} (d : Diagram P (l ++ s :: r) []) :
    Diagram P (s :: (r ++ l)) [] :=
  (rotatePrefix l (s :: r) d).cast (by simp) rfl

theorem labels_exposePort {l r : List S} {s : S} (d : Diagram P (l ++ s :: r) []) :
    d.exposePort.labels = d.labels :=
  (labels_cast _ _ _).trans (labels_rotatePrefix _ _ _)

def glueFirst {u v : List S} {s : S} (d : Diagram P (s :: u) []) (e : Diagram P (s :: v) []) :
    Diagram P (u ++ v) [] :=
  (d.bendFirst.tensor (identity v)).comp e

theorem labels_glueFirst {u v : List S} {s : S}
    (d : Diagram P (s :: u) []) (e : Diagram P (s :: v) []) :
    (d.glueFirst e).labels = d.labels ++ e.labels := by
  simp [glueFirst, labels, labels_bendFirst]

def splicePorts {l r l' r' : List S} {s : S}
    (d : Diagram P (l ++ s :: r) []) (e : Diagram P (l' ++ s :: r') []) :
    Diagram P ((r ++ l) ++ (r' ++ l')) [] :=
  d.exposePort.glueFirst e.exposePort

theorem labels_splicePorts {l r l' r' : List S} {s : S}
    (d : Diagram P (l ++ s :: r) []) (e : Diagram P (l' ++ s :: r') []) :
    (d.splicePorts e).labels = d.labels ++ e.labels := by
  rw [splicePorts, labels_glueFirst, labels_exposePort, labels_exposePort]

theorem size_splicePorts {l r l' r' : List S} {s : S}
    (d : Diagram P (l ++ s :: r) []) (e : Diagram P (l' ++ s :: r') []) :
    (d.splicePorts e).size = d.size + e.size := by
  simp only [size, labels_splicePorts, List.length_append]

theorem sign_splicePorts {l r l' r' : List S} {s : S}
    (d : Diagram P (l ++ s :: r) []) (e : Diagram P (l' ++ s :: r') []) :
    (d.splicePorts e).sign = d.sign + e.sign := by
  simp only [sign, labels_splicePorts, List.map_append, List.sum_append]

end ThomGame.Pictures.Diagram
