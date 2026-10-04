module

public import ThomGame.Pictures.VerticalBoundaryComponents
public import ThomGame.Pictures.ComponentTransport

/-!
# Additivity of the actual dart Euler defect

For vertical composition, each successive leaf splice preserves the
defect. The component/circuit equivalence used at that step was proved
for that actual partial seam. Tensor composition uses disjoint sums.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w z : List S}

theorem fullPartialSeam_eulerDefect (G : PortGraph P u v) (H : PortGraph P v w)
    (hG : G.BoundarySeesComponents) (hH : H.BoundarySeesComponents)
    (nG : G.BoundaryNoncrossing) (nH : H.BoundaryNoncrossing) (k : Nat) (hk : k ≤ v.length) :
    eulerDefect (Equiv.sumCongr G.pairing.perm H.pairing.perm) (fullPartialSeam G H k) =
      eulerDefect G.pairing.perm G.circuitStep + eulerDefect H.pairing.perm H.circuitStep := by
  induction k with
  | zero => rw [fullPartialSeam_zero, eulerDefect_sum]
  | succ k ih =>
    have hik : k < v.length := by omega
    let i : Fin v.length := ⟨k, hik⟩
    rw [fullPartialSeam_step G H i]
    have hs := eulerDefect_leaf_splice (Equiv.sumCongr G.pairing.perm H.pairing.perm)
      (fullPartialSeam G H k) (a := .inl (.bottom i)) (b := .inr (.top i)) (by simp)
      (fullPartialSeam_leaves G H k _ (retainedFullSeamLeft G H i).property)
      (fullPartialSeam_seesComponents G H hG hH nG nH k (by omega)
        (retainedFullSeamLeft G H i) (retainedFullSeamRight G H i))
    exact hs.trans (ih (by omega))

theorem eulerDefect_comp (G : PortGraph P u v) (H : PortGraph P v w)
    (hG : G.BoundarySeesComponents) (hH : H.BoundarySeesComponents)
    (nG : G.BoundaryNoncrossing) (nH : H.BoundaryNoncrossing) :
    eulerDefect (G.comp H).pairing.perm (G.comp H).circuitStep =
      eulerDefect G.pairing.perm G.circuitStep + eulerDefect H.pairing.perm H.circuitStep := by
  exact (eulerDefect_congr (Equiv.sumCongr G.pairing.perm H.pairing.perm)
    (fullPartialSeam G H v.length) (G.comp H).pairing.perm (G.comp H).circuitStep
    (compPorts G H) (twin_compPorts G H) (fullPartialSeam_all G H)).symm.trans
      (fullPartialSeam_eulerDefect G H hG hH nG nH v.length le_rfl)

theorem eulerDefect_tensor (G : PortGraph P u v) (H : PortGraph P w z) :
    eulerDefect (G.tensor H).pairing.perm (G.tensor H).circuitStep =
      eulerDefect G.pairing.perm G.circuitStep + eulerDefect H.pairing.perm H.circuitStep := by
  exact (eulerDefect_congr (Equiv.sumCongr G.pairing.perm H.pairing.perm)
    (Equiv.sumCongr G.circuitStep H.circuitStep) (G.tensor H).pairing.perm (G.tensor H).circuitStep
    (tensorPorts G H) (twin_tensorPorts G H) (circuitStep_tensorPorts G H)).symm.trans
      (eulerDefect_sum _ _ _ _)

end ThomGame.Pictures.PortGraph
