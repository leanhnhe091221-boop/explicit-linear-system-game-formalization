module

public import ThomGame.Groups.PrimeFiveCoverCyclicGeneration
public import Mathlib.Data.Finset.Image

/-! A concrete finite generating set: the union of the three actual cyclic root subgroups. -/

@[expose] public noncomputable section
namespace ThomGame.PrimeFiveRankThreeCover

open Compressor

def rootGeneratingSet (d : Nat) : Finset (Cover d) := by
  classical
  letI := Fintype.ofFinite (Σ c : Axis, rootSubgroup d (cyclicRoot c))
  exact Finset.univ.image (fun g : Σ c : Axis, rootSubgroup d (cyclicRoot c) => g.2.val)

theorem mem_rootGeneratingSet (d : Nat) (g : Cover d) :
    g ∈ rootGeneratingSet d ↔ ∃ c : Axis, g ∈ rootSubgroup d (cyclicRoot c) := by
  classical
  simp only [rootGeneratingSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨c, h⟩, rfl⟩
    exact ⟨c, h.property⟩
  · rintro ⟨c, hg⟩
    exact ⟨⟨c, ⟨g, hg⟩⟩, rfl⟩

theorem one_mem_rootGeneratingSet (d : Nat) : (1 : Cover d) ∈ rootGeneratingSet d :=
  (mem_rootGeneratingSet d 1).mpr ⟨0, (rootSubgroup d (cyclicRoot 0)).one_mem⟩

theorem rootGeneratingSet_nonempty (d : Nat) : (rootGeneratingSet d).Nonempty :=
  ⟨1, one_mem_rootGeneratingSet d⟩

theorem rootGeneratingSet_generates (d : Nat) :
    Subgroup.closure (rootGeneratingSet d : Set (Cover d)) = ⊤ := by
  apply top_unique
  rw [← cyclicRootSubgroups_generate d]
  apply iSup_le
  intro c g hg
  exact Subgroup.subset_closure ((mem_rootGeneratingSet d g).mpr ⟨c, hg⟩)

end ThomGame.PrimeFiveRankThreeCover
