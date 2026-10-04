module

public import ThomGame.Pictures.CyclicBlockWords

/-! # Cycle words from the actual ordered incidences at a vertex -/

@[expose] public section
namespace ThomGame.Pictures.CyclicBlock

open Equiv

variable {D : Type*} [DecidableEq D] {n : Nat}

theorem formPerm_ofFn (f : Fin n → D) (hf : Function.Injective f) (i : Fin n) :
    (List.ofFn f).formPerm (f i) = f (finRotate n i) := by
  let : NeZero n := i.neZero
  have hp := List.formPerm_apply_getElem (List.ofFn f) (List.nodup_ofFn.mpr hf)
    i.val (by simpa only [List.length_ofFn] using i.isLt)
  simp only [List.getElem_ofFn, List.length_ofFn] at hp
  refine hp.trans (congrArg f ?_)
  apply Fin.ext
  simp only [finRotate_apply, Fin.val_add]
  change (i.val + 1) % n = (i.val + 1 % n) % n
  exact (Nat.add_mod_mod _ _ _).symm

theorem IsCycleWord.ofFn (r : Perm D) (f : Fin n → D) (hf : Function.Injective f)
    (hn : 0 < n) (hr : ∀ i, r (f i) = f (finRotate n i)) : IsCycleWord r (List.ofFn f) where
  nodup := List.nodup_ofFn.mpr hf
  nonempty hw := by have := congrArg List.length hw; simp only [List.length_ofFn, List.length_nil] at this; omega
  rotation x hx := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (hr i).trans (formPerm_ofFn f hf i).symm

theorem IsCycleWord.reverse {r : Perm D} {w : List D} (h : IsCycleWord r w) :
    IsCycleWord r.symm w.reverse where
  nodup := by simpa only [List.nodup_reverse] using h.nodup
  nonempty hw := h.nonempty (List.reverse_eq_nil_iff.mp hw)
  rotation x hx := by
    have hm : x ∈ w := List.mem_reverse.mp hx
    have hy : w.formPerm⁻¹ x ∈ w := by
      simpa only [zpow_neg_one] using List.form_perm_zpow_apply_mem_imp_mem w x hm (-1)
    rw [List.formPerm_reverse]
    apply r.injective
    rw [r.apply_symm_apply, h.rotation _ hy]
    exact (w.formPerm.apply_symm_apply x).symm

end ThomGame.Pictures.CyclicBlock
