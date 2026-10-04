module

public import ThomGame.Pictures.BoundaryReturn
public import ThomGame.Pictures.CircuitComposition
public import ThomGame.Pictures.ReturnPaths

/-!
# Boundary visits under horizontal composition

Appending two diagrams preserves the entire boundary-successor
permutation in each summand, with the actual appended boundary indices.
This is a statement about cyclic visits, not only about connectedness.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w z : List S}

def tensorBoundaryLeft : BoundaryIndex u v → BoundaryIndex (u ++ w) (v ++ z)
  | .inl i => .inl (appendIndex u w (.inl i))
  | .inr i => .inr (appendIndex v z (.inl i))

def tensorBoundaryRight : BoundaryIndex w z → BoundaryIndex (u ++ w) (v ++ z)
  | .inl i => .inl (appendIndex u w (.inr i))
  | .inr i => .inr (appendIndex v z (.inr i))

theorem tensor_boundary_left (G : PortGraph P u v) (H : PortGraph P w z) (i : BoundaryIndex u v) :
    tensorPorts G H (.inl (G.boundaryDart i)) =
      (G.tensor H).boundaryDart (tensorBoundaryLeft i) := by
  cases i <;> rfl

theorem tensor_boundary_right (G : PortGraph P u v) (H : PortGraph P w z) (i : BoundaryIndex w z) :
    tensorPorts G H (.inr (H.boundaryDart i)) =
      (G.tensor H).boundaryDart (tensorBoundaryRight i) := by
  cases i <;> rfl

theorem tensor_boundary_iff_left (G : PortGraph P u v) (H : PortGraph P w z) (a : G.Dart) :
    (G.tensor H).IsBoundary (tensorPorts G H (.inl a)) ↔ G.IsBoundary a := by
  cases a <;> rfl

theorem tensor_boundary_iff_right (G : PortGraph P u v) (H : PortGraph P w z) (a : H.Dart) :
    (G.tensor H).IsBoundary (tensorPorts G H (.inr a)) ↔ H.IsBoundary a := by
  cases a <;> rfl

theorem boundaryNext_tensor_left (G : PortGraph P u v) (H : PortGraph P w z)
    (i : BoundaryIndex u v) :
    (G.tensor H).boundaryNext (tensorBoundaryLeft i) = tensorBoundaryLeft (G.boundaryNext i) := by
  have he := MarkedReturn.perm_preserved_of_commutes (G.tensor H).circuitStep
    (G.tensor H).IsBoundary G.circuitStep G.IsBoundary (fun a => tensorPorts G H (.inl a))
    (fun a => circuitStep_tensorPorts G H (.inl a)) (tensor_boundary_iff_left G H) (G.boundaryPorts i)
  have hi : (⟨tensorPorts G H (.inl (G.boundaryPorts i).val),
      (tensor_boundary_iff_left G H _).mpr (G.boundaryPorts i).property⟩ :
      {a : (G.tensor H).Dart // (G.tensor H).IsBoundary a}) =
        (G.tensor H).boundaryPorts (tensorBoundaryLeft i) := by
    cases i <;> rfl
  rw [hi, G.boundaryPorts_next, (G.tensor H).boundaryPorts_next] at he
  apply (G.tensor H).boundaryDart.injective
  change tensorPorts G H (.inl (G.boundaryDart (G.boundaryNext i))) =
    (G.tensor H).boundaryDart ((G.tensor H).boundaryNext (tensorBoundaryLeft i)) at he
  exact he.symm.trans (tensor_boundary_left G H _)

theorem boundaryNext_tensor_right (G : PortGraph P u v) (H : PortGraph P w z)
    (i : BoundaryIndex w z) :
    (G.tensor H).boundaryNext (tensorBoundaryRight i) = tensorBoundaryRight (H.boundaryNext i) := by
  have he := MarkedReturn.perm_preserved_of_commutes (G.tensor H).circuitStep
    (G.tensor H).IsBoundary H.circuitStep H.IsBoundary (fun a => tensorPorts G H (.inr a))
    (fun a => circuitStep_tensorPorts G H (.inr a)) (tensor_boundary_iff_right G H) (H.boundaryPorts i)
  have hi : (⟨tensorPorts G H (.inr (H.boundaryPorts i).val),
      (tensor_boundary_iff_right G H _).mpr (H.boundaryPorts i).property⟩ :
      {a : (G.tensor H).Dart // (G.tensor H).IsBoundary a}) =
        (G.tensor H).boundaryPorts (tensorBoundaryRight i) := by
    cases i <;> rfl
  rw [hi, H.boundaryPorts_next, (G.tensor H).boundaryPorts_next] at he
  apply (G.tensor H).boundaryDart.injective
  change tensorPorts G H (.inr (H.boundaryDart (H.boundaryNext i))) =
    (G.tensor H).boundaryDart ((G.tensor H).boundaryNext (tensorBoundaryRight i)) at he
  exact he.symm.trans (tensor_boundary_right G H _)

end ThomGame.Pictures.PortGraph
