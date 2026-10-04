module

public import ThomGame.Pictures.FullSeamReturn

/-!
# Actual vertical composition preserves boundary component detection

In the same-circuit case, the ordered noncrossing boundary theorem
makes the next seam pair consecutive in the retained return. This
discharges the local component-surgery hypothesis at every real seam.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}
variable (G : PortGraph P u v) (H : PortGraph P v w)

def retainedFullSeamLeft (i : Fin v.length) : Subtype (FullSeamRemaining G H i.val) :=
  ⟨.inl (.bottom i), le_rfl⟩

def retainedFullSeamRight (i : Fin v.length) : Subtype (FullSeamRemaining G H i.val) :=
  ⟨.inr (.top i), le_rfl⟩

theorem numberedFullBoundary_left_eq (i : Fin v.length) :
    numberedFullBoundary G H i.val (retainedSeamLeft u v w i) = retainedFullSeamLeft G H i :=
  Subtype.ext (numberedFullBoundary_left G H i)

theorem numberedFullBoundary_right_eq (i : Fin v.length) :
    numberedFullBoundary G H i.val (retainedSeamRight u v w i) = retainedFullSeamRight G H i :=
  Subtype.ext (numberedFullBoundary_right G H i)

/-- Adjacency in the numbered boundary gives the actual full-dart first
return between seam leaves when they lie on the same circuit. -/
theorem fullPartialSeam_next_of_sameCycle (hG : G.BoundaryNoncrossing) (hH : H.BoundaryNoncrossing)
    (i : Fin v.length)
    (hs : (fullPartialSeam G H i.val).SameCycle (.inl (.bottom i)) (.inr (.top i))) :
    perm (fullPartialSeam G H i.val) (FullSeamRemaining G H i.val) (retainedFullSeamLeft G H i) =
      retainedFullSeamRight G H i := by
  have hc := (numberedFullBoundary_sameCycle G H i.val i.val
    (retainedSeamLeft u v w i) (retainedSeamRight u v w i)).mpr
      (by simpa only [numberedFullBoundary_left, numberedFullBoundary_right] using hs)
  have hn := (numberedPartialSeam_noncrossing G H hG hH i.val (Nat.le_of_lt i.isLt)).follows.apply_of_adjacent
    (retainedSeam_adjacent u v w i) hc
  have he := numberedFullBoundary_next G H i.val i.val (retainedSeamLeft u v w i)
  rwa [hn, numberedFullBoundary_left_eq, numberedFullBoundary_right_eq] at he

theorem fullPartialSeam_seesComponents
    (hG : G.BoundarySeesComponents) (hH : H.BoundarySeesComponents)
    (nG : G.BoundaryNoncrossing) (nH : H.BoundaryNoncrossing) (k : Nat) (hk : k ≤ v.length) :
    SeesComponents (Equiv.sumCongr G.pairing.perm H.pairing.perm)
      (fullPartialSeam G H k) (FullSeamRemaining G H k) := by
  induction k with
  | zero =>
    rw [fullPartialSeam_zero]
    exact (SeesComponents.sum G.pairing.perm G.circuitStep H.pairing.perm H.circuitStep hG hH).restrict
      (fun x hx => (fullSeamRemaining_zero G H x).mp hx)
  | succ k ih =>
    have hik : k < v.length := by omega
    let i : Fin v.length := ⟨k, hik⟩
    have hs := (ih (by omega)).splice_restrict
      (retainedFullSeamLeft G H i) (retainedFullSeamRight G H i)
      (fullPartialSeam_leaves G H k _ (retainedFullSeamLeft G H i).property)
      (fullSeamRemaining_mono G H k)
      (show ¬ FullSeamRemaining G H (k + 1) (retainedFullSeamLeft G H i).val from Nat.not_succ_le_self k)
      (fullPartialSeam_next_of_sameCycle G H nG nH i)
    rw [fullPartialSeam_step G H i]
    exact hs

theorem boundarySeesComponents_comp
    (hG : G.BoundarySeesComponents) (hH : H.BoundarySeesComponents)
    (nG : G.BoundaryNoncrossing) (nH : H.BoundaryNoncrossing) : (G.comp H).BoundarySeesComponents := by
  exact (fullPartialSeam_seesComponents G H hG hH nG nH v.length le_rfl).transport
    (compPorts G H) (twin_compPorts G H) (fullPartialSeam_all G H) (fullSeamRemaining_all G H)

end ThomGame.Pictures.PortGraph
