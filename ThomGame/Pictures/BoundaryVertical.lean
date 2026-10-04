module

public import ThomGame.Pictures.BoundaryComposition
public import ThomGame.Pictures.ReturnPathOperations

/-!
# Vertical composition computed entirely on boundary ports

Take the disjoint union of the two boundary-successor permutations,
exchange the two occurrences of every seam index, then take the first
return to the remaining outer ports. This computes exactly the boundary
successor of `PortGraph.comp`, independently of its internal darts.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open MarkedReturn

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}

abbrev SeamBoundary (u v w : List S) := BoundaryIndex u v ⊕ BoundaryIndex v w

def boundarySeamSwap : Equiv.Perm (SeamBoundary u v w) where
  toFun
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl i) => .inl (.inr i)
    | b => b
  invFun
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl i) => .inl (.inr i)
    | b => b
  left_inv b := by rcases b with (i | i) | (i | i) <;> rfl
  right_inv b := by rcases b with (i | i) | (i | i) <;> rfl

def IsOuter : SeamBoundary u v w → Prop
  | .inl (.inl _) => True
  | .inr (.inr _) => True
  | _ => False

def outerPorts : BoundaryIndex u w ≃ {b : SeamBoundary u v w // IsOuter b} where
  toFun
    | .inl i => ⟨.inl (.inl i), trivial⟩
    | .inr i => ⟨.inr (.inr i), trivial⟩
  invFun b := match b with
    | ⟨.inl (.inl i), _⟩ => .inl i
    | ⟨.inr (.inr i), _⟩ => .inr i
    | ⟨.inl (.inr _), h⟩ => h.elim
    | ⟨.inr (.inl _), h⟩ => h.elim
  left_inv i := by cases i <;> rfl
  right_inv b := by
    rcases b with ⟨(i | i) | (i | i), h⟩ <;> first | rfl | exact h.elim

noncomputable def boundarySeamCircuit (G : PortGraph P u v) (H : PortGraph P v w) :
    Equiv.Perm (SeamBoundary u v w) :=
  boundarySeamSwap * Equiv.sumCongr G.boundaryNext H.boundaryNext

noncomputable def verticalBoundaryNext (G : PortGraph P u v) (H : PortGraph P v w) :
    Equiv.Perm (BoundaryIndex u w) :=
  (outerPorts.trans (MarkedReturn.perm (boundarySeamCircuit G H) IsOuter)).trans outerPorts.symm

def oldBoundaryDart (G : PortGraph P u v) (H : PortGraph P v w) :
    SeamBoundary u v w → G.Dart ⊕ H.Dart := Sum.map G.boundaryDart H.boundaryDart

def seamBoundaryDart (G : PortGraph P u v) (H : PortGraph P v w) :
    SeamBoundary u v w → (G.comp H).Dart := fun b => compPorts G H (oldBoundaryDart G H b)

def OuterDart (G : PortGraph P u v) (H : PortGraph P v w) : G.Dart ⊕ H.Dart → Prop
  | .inl (.top _) => True
  | .inr (.bottom _) => True
  | _ => False

theorem outerDart_isBoundary (G : PortGraph P u v) (H : PortGraph P v w) (a : G.Dart ⊕ H.Dart)
    (ha : OuterDart G H a) : Sum.elim G.IsBoundary H.IsBoundary a := by
  rcases a with a | a <;> cases a <;> trivial

theorem comp_boundary_iff_outerDart (G : PortGraph P u v) (H : PortGraph P v w)
    (a : G.Dart ⊕ H.Dart) : (G.comp H).IsBoundary (compPorts G H a) ↔ OuterDart G H a := by
  rcases a with a | a <;> cases a <;> rfl

theorem seamBoundaryDart_outer_iff (G : PortGraph P u v) (H : PortGraph P v w)
    (b : SeamBoundary u v w) : (G.comp H).IsBoundary (seamBoundaryDart G H b) ↔ IsOuter b := by
  rcases b with (i | i) | (i | i) <;> rfl

theorem seamBoundaryDart_outerPorts (G : PortGraph P u v) (H : PortGraph P v w)
    (i : BoundaryIndex u w) :
    seamBoundaryDart G H (outerPorts (v := v) i).val = (G.comp H).boundaryDart i := by
  cases i <;> rfl

theorem boundary_hit (G : PortGraph P u v) (i : BoundaryIndex u v) :
    Hit G.circuitStep G.IsBoundary (G.boundaryDart i) (G.boundaryDart (G.boundaryNext i)) := by
  have h := hit_perm G.circuitStep G.IsBoundary (G.boundaryPorts i)
  rw [G.boundaryPorts_next] at h
  exact h

theorem sumBoundary_hit (G : PortGraph P u v) (H : PortGraph P v w) (b : SeamBoundary u v w) :
    Hit (Equiv.sumCongr G.circuitStep H.circuitStep) (Sum.elim G.IsBoundary H.IsBoundary)
      (oldBoundaryDart G H b)
      (oldBoundaryDart G H (Equiv.sumCongr G.boundaryNext H.boundaryNext b)) := by
  cases b with
  | inl i => exact (G.boundary_hit i).map Sum.inl (fun _ => rfl) (fun _ => Iff.rfl)
  | inr i => exact (H.boundary_hit i).map Sum.inr (fun _ => rfl) (fun _ => Iff.rfl)

theorem seamSwap_fixed_off_boundary (G : PortGraph P u v) (H : PortGraph P v w)
    (a : G.Dart ⊕ H.Dart) (ha : ¬ Sum.elim G.IsBoundary H.IsBoundary a) : seamSwap G H a = a := by
  rcases a with a | a <;> cases a <;> first | rfl | exact (ha trivial).elim

theorem seamSwap_oldBoundaryDart (G : PortGraph P u v) (H : PortGraph P v w)
    (b : SeamBoundary u v w) :
    seamSwap G H (oldBoundaryDart G H b) = oldBoundaryDart G H (boundarySeamSwap b) := by
  rcases b with (i | i) | (i | i) <;> rfl

/-- Every reduced boundary step expands to a genuine path in the composed
graph, with no outer boundary port in its interior. -/
theorem boundarySeam_hit (G : PortGraph P u v) (H : PortGraph P v w) (b : SeamBoundary u v w) :
    Hit (G.comp H).circuitStep (G.comp H).IsBoundary (seamBoundaryDart G H b)
      (seamBoundaryDart G H (boundarySeamCircuit G H b)) := by
  have ht := (sumBoundary_hit G H b).twist_targets (seamSwap G H) (seamSwap_fixed_off_boundary G H)
  rw [seamSwap_oldBoundaryDart] at ht
  have ho := ht.weaken (outerDart_isBoundary G H)
  exact ho.map (compPorts G H) (circuitStep_compPorts G H) (comp_boundary_iff_outerDart G H)

theorem outerPorts_verticalNext (G : PortGraph P u v) (H : PortGraph P v w)
    (i : BoundaryIndex u w) :
    MarkedReturn.perm (boundarySeamCircuit G H) IsOuter (outerPorts i) =
      outerPorts (verticalBoundaryNext G H i) := by
  change _ = outerPorts (outerPorts.symm _)
  rw [Equiv.apply_symm_apply]
  rfl

/-- The complete vertical boundary formula uses only the two old boundary
permutations and the numbered seams. -/
theorem boundaryNext_comp (G : PortGraph P u v) (H : PortGraph P v w) :
    (G.comp H).boundaryNext = verticalBoundaryNext G H := by
  apply Equiv.ext
  intro i
  have he := perm_preserved_of_paths (G.comp H).circuitStep (G.comp H).IsBoundary
    (boundarySeamCircuit G H) IsOuter (seamBoundaryDart G H) (boundarySeam_hit G H)
    (seamBoundaryDart_outer_iff G H) (outerPorts i)
  have hi : (⟨seamBoundaryDart G H (outerPorts i).val,
      (seamBoundaryDart_outer_iff G H _).mpr (outerPorts i).property⟩ :
      {a : (G.comp H).Dart // (G.comp H).IsBoundary a}) = (G.comp H).boundaryPorts i := by
    cases i <;> rfl
  rw [hi, (G.comp H).boundaryPorts_next, outerPorts_verticalNext] at he
  apply (G.comp H).boundaryDart.injective
  exact he.symm.trans (seamBoundaryDart_outerPorts G H _)

theorem boundaryNext_comp_congr {G G' : PortGraph P u v} {H H' : PortGraph P v w}
    (hG : G.boundaryNext = G'.boundaryNext) (hH : H.boundaryNext = H'.boundaryNext) :
    (G.comp H).boundaryNext = (G'.comp H').boundaryNext := by
  rw [boundaryNext_comp, boundaryNext_comp]
  unfold verticalBoundaryNext boundarySeamCircuit
  rw [hG, hH]

end ThomGame.Pictures.PortGraph
