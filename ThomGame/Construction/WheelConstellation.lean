module

public import ThomGame.Construction.WheelRetractions
public import ThomGame.Construction.WheelPentagonRetractions
public import ThomGame.Finite.WheelCycleIncidence
public import ThomGame.Finite.HypergraphConstellation

/-! # The actual wheel cycles form a constellation -/

@[expose] public section
namespace ThomGame.Construction

abbrev WheelCycleIndex := WheelIndex ⊕ ((r : WheelIndex) × Fin (wheelFamily.size r))

def wheelCycles : WheelCycleIndex → Hypergraph.Cycle system.hypergraph
  | .inl r => centralWheelCycle r
  | .inr ⟨r, j⟩ => pentagonWheelCycle r j

def oddWheelCycle : WheelCycleIndex := .inr ⟨none, 0⟩

def wheelCycleSun (i : WheelCycleIndex) : (wheelCycles i).SunNeighbourhood :=
  match i with
  | .inl r => (centralWheelStellar r).neighbourhood
  | .inr ⟨r, j⟩ => pentagonWheelSunNeighbourhood r j

theorem wheelCycle_stellar_of_ne_odd (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle) :
    Nonempty ((wheelCycles i).Stellar system.rhs) := by
  rcases i with r | ⟨r, j⟩
  · exact ⟨centralWheelStellar r⟩
  · refine ⟨pentagonWheelStellar r j ?_⟩
    intro h
    have he := congrArg (fun row : Row => (⟨row.1, row.2.1⟩ : (r : WheelIndex) × Fin (wheelFamily.size r))) h
    exact hi (congrArg Sum.inr he)

theorem wheelCycle_eq_odd_of_not_stellar (i : WheelCycleIndex)
    (hi : ¬ Nonempty ((wheelCycles i).Stellar system.rhs)) : i = oddWheelCycle := by
  by_contra h
  exact hi (wheelCycle_stellar_of_ne_odd i h)

theorem pentagon_private_edge (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.HasPrivateEdge wheelCycles (.inr ⟨r, j⟩) := by
  refine ⟨wheelFamily.aux r j 0, ⟨0, rfl⟩, ?_⟩
  rintro (s | ⟨s, i⟩) he
  · change wheelFamily.aux r j 0 ∈ wheelFamily.centralEdges s at he
    have h := (wheelFamily.aux_mem_central r s j 0).mp he
    cases h.2
  · change wheelFamily.aux r j 0 ∈ wheelFamily.pentagonEdges s i at he
    exact congrArg Sum.inr ((wheelFamily.a_mem_pentagon r s j i).mp he)

theorem wheelCycles_intersection_unique (i j : WheelCycleIndex) (hij : i ≠ j)
    (e f : Col) (hei : e ∈ Set.range (wheelCycles i).edge) (hej : e ∈ Set.range (wheelCycles j).edge)
    (hfi : f ∈ Set.range (wheelCycles i).edge) (hfj : f ∈ Set.range (wheelCycles j).edge) : e = f := by
  rcases i with r | ⟨r, k⟩ <;> rcases j with s | ⟨s, l⟩
  · change e ∈ wheelFamily.centralEdges r at hei
    change e ∈ wheelFamily.centralEdges s at hej
    obtain ⟨k, rfl⟩ := hei
    exact (hij (congrArg Sum.inl ((wheelFamily.aux_mem_central r s k 3).mp hej).1)).elim
  · have he := (wheelFamily.central_pentagon_intersection r s l e).mp ⟨hei, hej⟩
    have hf := (wheelFamily.central_pentagon_intersection r s l f).mp ⟨hfi, hfj⟩
    exact he.2.trans hf.2.symm
  · have he := (wheelFamily.central_pentagon_intersection s r k e).mp ⟨hej, hei⟩
    have hf := (wheelFamily.central_pentagon_intersection s r k f).mp ⟨hfj, hfi⟩
    exact he.2.trans hf.2.symm
  · have hrs := wheelFamily.pentagon_edges_same_wheel hei hej
    subst s
    have hkl : k ≠ l := by intro h; subst l; exact hij rfl
    exact wheelFamily.pentagon_intersection_unique r
      (Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r)) k l hkl hei hej hfi hfj

theorem oddWheelCycle_covered (k : Fin (wheelCycles oddWheelCycle).length) (hk : 2 ≤ k.val) :
    ∃ j, Nonempty ((wheelCycles j).Stellar system.rhs) ∧
      (wheelCycles oddWheelCycle).edge k ∈ Set.range (wheelCycles j).edge := by
  change Fin 5 at k
  fin_cases k
  · change 2 ≤ 0 at hk
    omega
  · change 2 ≤ 1 at hk
    omega
  · exact ⟨.inr ⟨none, 1⟩, ⟨pentagonWheelStellar none 1 (by decide +kernel)⟩, ⟨4, rfl⟩⟩
  · exact ⟨.inl none, ⟨centralWheelStellar none⟩, ⟨0, rfl⟩⟩
  · exact ⟨.inr ⟨none, 3⟩, ⟨pentagonWheelStellar none 3 (by decide +kernel)⟩, ⟨2, rfl⟩⟩

def wheelConstellation : Hypergraph.Constellation wheelCycles system.rhs where
  neighbourhood := wheelCycleSun
  stellar_or_covered i := by
    by_cases hi : i = oddWheelCycle
    · subst i
      exact Or.inr oddWheelCycle_covered
    · exact Or.inl (wheelCycle_stellar_of_ne_odd i hi)
  private_or_neighbour := by
    rintro (r | ⟨r, j⟩)
    · refine Or.inr ⟨.inr ⟨r, 0⟩, by simp, ?_, pentagon_private_edge r 0⟩
      exact ⟨wheelFamily.aux r 0 3, ⟨0, rfl⟩, ⟨3, rfl⟩⟩
    · exact Or.inl (pentagon_private_edge r j)
  intersection_unique := wheelCycles_intersection_unique
  nonstellar_disjoint i j hij hi hj := by
    exact (hij ((wheelCycle_eq_odd_of_not_stellar i hi).trans
      (wheelCycle_eq_odd_of_not_stellar j hj).symm)).elim

def wheelCycleZeroStellar (i : WheelCycleIndex) : (wheelCycles i).Stellar (fun _ => 0) := by
  rcases i with r | ⟨r, j⟩
  · exact {
      retraction := centralWheelRetraction r
      vertex_eq := fun _ => rfl
      rim_eq := fun _ => rfl
      rhs_zero := fun _ => rfl }
  · exact {
      retraction := pentagonWheelRetraction r j
      vertex_eq := fun _ => rfl
      rim_eq := fun _ => rfl
      rhs_zero := fun _ => rfl }

def homogeneousWheelConstellation : Hypergraph.Constellation wheelCycles (fun _ => 0) :=
  wheelConstellation.withAllStellar _ wheelCycleZeroStellar

end ThomGame.Construction
