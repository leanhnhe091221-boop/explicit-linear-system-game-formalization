module

public import ThomGame.Groups.PrimeFiveCoverRootSubgroups

/-! The three cyclic root subgroups generate the actual cover. -/

@[expose] public section
namespace ThomGame.PrimeFiveRankThreeCover

open Compressor

theorem right_cyclicRoot : ∀ c : Axis, right (cyclicRoot c) = cyclicRoot (finRotate 3 c) := by decide +kernel

theorem cyclic_or_across : ∀ r : Root, ∃ c : Axis, r = cyclicRoot c ∨ r = across (cyclicRoot c) := by decide +kernel

namespace Model

variable {d : Nat} {G : Type*} [Group G] (M : Model d G)

theorem x_mem_cyclicSup (r : Root) (m : Coefficient d) :
    M.x r m ∈ ⨆ c : Axis, M.rootSubgroup (cyclicRoot c) := by
  obtain ⟨c, hc | hc⟩ := cyclic_or_across r
  · rw [hc]
    exact (le_iSup (fun c : Axis => M.rootSubgroup (cyclicRoot c)) c) (M.x_mem_rootSubgroup _ m)
  · rw [hc, ← M.e2]
    let K := ⨆ c : Axis, M.rootSubgroup (cyclicRoot c)
    have h1 : M.x (cyclicRoot c) m ∈ K := (le_iSup (fun c : Axis => M.rootSubgroup (cyclicRoot c)) c) (M.x_mem_rootSubgroup _ m)
    have h2 : M.x (right (cyclicRoot c)) none ∈ K := by
      rw [right_cyclicRoot]
      exact (le_iSup (fun c : Axis => M.rootSubgroup (cyclicRoot c)) (finRotate 3 c)) (M.x_mem_rootSubgroup _ none)
    exact K.mul_mem (K.mul_mem (K.mul_mem h1 h2) (K.inv_mem h1)) (K.inv_mem h2)

theorem range_eq_cyclicSup : M.toHom.range = ⨆ c : Axis, M.rootSubgroup (cyclicRoot c) := by
  apply le_antisymm
  · rw [M.range_toHom]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r, m⟩, rfl⟩
    exact M.x_mem_cyclicSup r m
  · apply iSup_le
    intro c
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨m, rfl⟩
    exact ⟨of d (cyclicRoot c) m, M.toHom_of _ _⟩

end Model

theorem cyclicRootSubgroups_generate (d : Nat) :
    (⨆ c : Axis, rootSubgroup d (cyclicRoot c)) = ⊤ := by
  apply top_unique
  intro x _
  exact PresentedGroup.generated_by (relators d) _
    (fun g => (canonicalModel d).x_mem_cyclicSup g.1 g.2) x

end ThomGame.PrimeFiveRankThreeCover
