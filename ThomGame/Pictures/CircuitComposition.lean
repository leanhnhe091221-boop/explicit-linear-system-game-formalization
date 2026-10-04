module

public import ThomGame.Pictures.GraphComposition
public import ThomGame.Pictures.GraphRotation
public import ThomGame.Pictures.OrbitTransport
public import ThomGame.Pictures.PermutationSurgery

/-!
# Circuit permutations of actual graph composition

Horizontal composition is a disjoint union of circuit permutations.
Vertical composition exchanges the two former leaves at each numbered
seam, after the old circuit step. The ports and labels are exactly those
of `PortGraph.comp`; these are not abstract gluing hypotheses.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w z : List S}

/-- Exchange the former bottom and top leaves at every numbered seam. -/
def seamSwap (G : PortGraph P u v) (H : PortGraph P v w) :
    Equiv.Perm (G.Dart ⊕ H.Dart) where
  toFun
    | .inl (.bottom i) => .inr (.top i)
    | .inr (.top i) => .inl (.bottom i)
    | a => a
  invFun
    | .inl (.bottom i) => .inr (.top i)
    | .inr (.top i) => .inl (.bottom i)
    | a => a
  left_inv a := by rcases a with a | a <;> cases a <;> rfl
  right_inv a := by rcases a with a | a <;> cases a <;> rfl

theorem rotation_compPorts (G : PortGraph P u v) (H : PortGraph P v w)
    (a : G.Dart ⊕ H.Dart) :
    (G.comp H).rotation (compPorts G H a) =
      compPorts G H (seamSwap G H (Equiv.sumCongr G.rotation H.rotation a)) := by
  rcases a with a | a <;> cases a <;> rfl

theorem circuitStep_compPorts (G : PortGraph P u v) (H : PortGraph P v w)
    (a : G.Dart ⊕ H.Dart) :
    (G.comp H).circuitStep (compPorts G H a) =
      compPorts G H (seamSwap G H (Equiv.sumCongr G.circuitStep H.circuitStep a)) := by
  calc
    _ = (G.comp H).rotation (compPorts G H (Sum.map G.pairing.twin H.pairing.twin a)) :=
      congrArg (G.comp H).rotation (twin_compPorts G H a)
    _ = _ := (rotation_compPorts G H _).trans (by cases a <;> rfl)

noncomputable def compCircuitEquiv (G : PortGraph P u v) (H : PortGraph P v w) :
    FiniteReturn.Orbit (Equiv.sumCongr G.circuitStep H.circuitStep |>.trans (seamSwap G H)) ≃
      (G.comp H).Circuit :=
  FiniteReturn.orbitEquiv _ _ (compPorts G H) (circuitStep_compPorts G H)

theorem rotation_tensorPorts (G : PortGraph P u v) (H : PortGraph P w z)
    (a : G.Dart ⊕ H.Dart) :
    (G.tensor H).rotation (tensorPorts G H a) =
      tensorPorts G H (Equiv.sumCongr G.rotation H.rotation a) := by
  rcases a with a | a <;> cases a <;> rfl

theorem circuitStep_tensorPorts (G : PortGraph P u v) (H : PortGraph P w z)
    (a : G.Dart ⊕ H.Dart) :
    (G.tensor H).circuitStep (tensorPorts G H a) =
      tensorPorts G H (Equiv.sumCongr G.circuitStep H.circuitStep a) := by
  calc
    _ = (G.tensor H).rotation (tensorPorts G H (Sum.map G.pairing.twin H.pairing.twin a)) :=
      congrArg (G.tensor H).rotation (twin_tensorPorts G H a)
    _ = _ := (rotation_tensorPorts G H _).trans (by cases a <;> rfl)

noncomputable def tensorCircuitEquiv (G : PortGraph P u v) (H : PortGraph P w z) :
    (G.tensor H).Circuit ≃ G.Circuit ⊕ H.Circuit :=
  (FiniteReturn.orbitEquiv _ _ (tensorPorts G H) (circuitStep_tensorPorts G H)).symm.trans
    (FiniteReturn.sumOrbitEquiv G.circuitStep H.circuitStep)

theorem tensor_circuit_card (G : PortGraph P u v) (H : PortGraph P w z) :
    Fintype.card (G.tensor H).Circuit = Fintype.card G.Circuit + Fintype.card H.Circuit := by
  rw [Fintype.card_congr (tensorCircuitEquiv G H), Fintype.card_sum]

end ThomGame.Pictures.PortGraph
