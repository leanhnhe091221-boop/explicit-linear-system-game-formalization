module

public import ThomGame.Certificates.NetzerThomWordChecker

@[expose] public section
namespace ThomGame.Certificates.NetzerThom
open ThomGame.Analysis

private theorem exists_zip_right {α β : Type*} {xs : List α} {ys : List β}
    (hlen : ys.length = xs.length) {a : α} (ha : a ∈ xs) :
    ∃ b, (a,b) ∈ xs.zip ys := by
  rw [← List.map_fst_zip (l₁ := xs) (l₂ := ys) (by omega)] at ha
  obtain ⟨⟨a',b⟩, hab, haa⟩ := List.mem_map.mp ha
  change a' = a at haa
  subst a'
  exact ⟨b, hab⟩

structure WordClassSound (c : ResidualClass) : Prop where
  gram : ∀ ij ∈ c.pairs,
    RelatorEquality IntegralShear.relators (FreeGroup.mk (gramWord ij))
      (FreeGroup.mk (ntWord c.representative)) 240
  target : ∀ i ∈ c.terms,
    RelatorEquality IntegralShear.relators
      (FreeGroup.mk (ntWord (targetTerms.getD i ([],0)).1))
      (FreeGroup.mk (ntWord c.representative)) 240

theorem wordClassCheck_sound {c : ResidualClass} {p : WordClassPaths}
    (h : wordClassCheck c p = true) : WordClassSound c := by
  simp only [wordClassCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  constructor
  · intro ij hij
    obtain ⟨ss, hss⟩ := exists_zip_right h.1.1.1 hij
    exact checkedPath_sound (h.1.2 (ij,ss) hss)
  · intro i hi
    obtain ⟨ss, hss⟩ := exists_zip_right h.1.1.2 hi
    exact checkedPath_sound (h.2 (i,ss) hss)

end ThomGame.Certificates.NetzerThom
