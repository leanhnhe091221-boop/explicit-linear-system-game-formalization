module

public import ThomGame.Groups.IntegerRootGraph
public import ThomGame.Groups.IntegralShearRootSubgroups

/-! The actual vertex and edge subgroups in the six-root decomposition. -/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor IntegerRootGraph

def rootSpan (S : Finset Root) : Subgroup ShearGroup := ⨆ r ∈ S, rootSubgroup r

theorem rootSubgroup_le_rootSpan (S : Finset Root) (r : Root) (hr : r ∈ S) :
    rootSubgroup r ≤ rootSpan S := le_iSup_of_le r (le_iSup_of_le hr le_rfl)

theorem rootSpan_le (S : Finset Root) (K : Subgroup ShearGroup)
    (h : ∀ r ∈ S, rootSubgroup r ≤ K) : rootSpan S ≤ K :=
  iSup_le fun r => iSup_le fun hr => h r hr

theorem rootSpan_mono {S T : Finset Root} (h : S ⊆ T) : rootSpan S ≤ rootSpan T :=
  rootSpan_le S (rootSpan T) fun r hr => rootSubgroup_le_rootSpan T r (h hr)

def graphVertexRoots (r : Root) : Finset Root := {r, across r, reverse (right r)}

def graphEdgeRoots (r : Root) : Fin 4 → Finset Root :=
  ![{r, across r}, {across r}, {reverse (right r)}, {r, reverse (right r)}]

theorem graphEdgeRoots_subset_vertex : ∀ (r : Root) (i : Fin 4), graphEdgeRoots r i ⊆ graphVertexRoots r := by
  decide +kernel

theorem graphEdgeRoots_reverse : ∀ (r : Root) (i : Fin 4),
    graphEdgeRoots (neighbor r i) (reverseIndex i) = graphEdgeRoots r i := by decide +kernel

def graphVertexGroup (r : Root) : Subgroup ShearGroup := rootSpan (graphVertexRoots r)

def graphEdgeGroup (r : Root) (i : Fin 4) : Subgroup ShearGroup := rootSpan (graphEdgeRoots r i)

theorem graphVertexGroup_contains_root (r : Root) : rootSubgroup r ≤ graphVertexGroup r :=
  rootSubgroup_le_rootSpan _ r (by simp [graphVertexRoots])

theorem graphVertexGroup_eq_pair (r : Root) : graphVertexGroup r = rootPairSubgroup (across r) := by
  have ha : across (across r) = r := (show ∀ s : Root, across (across s) = s from by decide +kernel) r
  have hr : right (across r) = reverse (right r) :=
    (show ∀ s : Root, right (across s) = reverse (right s) from by decide +kernel) r
  have hcenter : rootSubgroup r ≤ rootPairSubgroup (across r) := by
    simpa only [ha] using rootPair_contains_center (across r)
  have hleft : rootSubgroup (across r) ≤ rootPairSubgroup (across r) := le_sup_left
  have hright : rootSubgroup (reverse (right r)) ≤ rootPairSubgroup (across r) := by
    rw [← hr]
    exact le_sup_right
  apply le_antisymm
  · apply rootSpan_le
    intro s hs
    simp only [graphVertexRoots, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hcenter
    · exact hleft
    · exact hright
  · change rootSubgroup (across r) ⊔ rootSubgroup (right (across r)) ≤ _
    apply sup_le
    · exact rootSubgroup_le_rootSpan _ _ (by simp [graphVertexRoots])
    · rw [hr]
      exact rootSubgroup_le_rootSpan _ _ (by simp [graphVertexRoots])

theorem graphEdgeGroup_reverse (r : Root) (i : Fin 4) :
    graphEdgeGroup (neighbor r i) (reverseIndex i) = graphEdgeGroup r i := by
  simp only [graphEdgeGroup, graphEdgeRoots_reverse]

theorem graphEdgeGroup_le_vertex (r : Root) (i : Fin 4) : graphEdgeGroup r i ≤ graphVertexGroup r :=
  rootSpan_mono (graphEdgeRoots_subset_vertex r i)

theorem graphEdgeGroup_le_neighbor (r : Root) (i : Fin 4) :
    graphEdgeGroup r i ≤ graphVertexGroup (neighbor r i) := by
  rw [← graphEdgeGroup_reverse r i]
  exact graphEdgeGroup_le_vertex _ _

theorem graphVertexGroups_generate : (⨆ r : Root, graphVertexGroup r) = ⊤ := by
  apply top_unique
  rw [← rootSubgroups_generate]
  apply iSup_le
  intro r
  exact (graphVertexGroup_contains_root r).trans (le_iSup _ r)

end ThomGame.IntegralShear
