module

public import ThomGame.Finite.WheelPentagon

/-! # Edge intersections among the actual wheel cycles -/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} (F : Family R V)

def centralEdges (r : R) : Set F.Col := Set.range (fun j => F.aux r j 3)
def pentagonEdges (r : R) (j : Fin (F.size r)) : Set F.Col := Set.range (F.pentagonRim r j)

theorem pentagon_mem_iff (r : R) (j : Fin (F.size r)) (e : F.Col) :
    e ∈ F.pentagonEdges r j ↔
      e = F.aux r j 0 ∨ e = F.aux r j 1 ∨ e = F.aux r j 2 ∨ e = F.aux r j 3 ∨
        e = F.aux r ((finRotate (F.size r)).symm j) 2 := by
  classical
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [pentagonRim]
  · rintro (h | h | h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
    · exact ⟨4, h.symm⟩

theorem aux_mem_central (r s : R) (j : Fin (F.size r)) (k : Fin 4) :
    F.aux r j k ∈ F.centralEdges s ↔ r = s ∧ k = 3 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp [centralEdges, aux, eq_comm]
  · have hsr := Ne.symm hrs
    simp [centralEdges, aux, hrs, hsr]

theorem a_mem_pentagon (r s : R) (j : Fin (F.size r)) (i : Fin (F.size s)) :
    F.aux r j 0 ∈ F.pentagonEdges s i ↔
      (⟨s, i⟩ : (t : R) × Fin (F.size t)) = ⟨r, j⟩ := by
  classical
  by_cases hsr : s = r
  · subst s
    simp [F.pentagon_mem_iff, aux, eq_comm]
  · have hrs := Ne.symm hsr
    simp [F.pentagon_mem_iff, aux, hrs, hsr]

theorem c_mem_pentagon (r : R) (i j : Fin (F.size r)) :
    F.aux r i 2 ∈ F.pentagonEdges r j ↔ i = j ∨ i = (finRotate (F.size r)).symm j := by
  classical
  simp [F.pentagon_mem_iff, aux]

theorem pentagon_edges_same_wheel {r s : R} {j : Fin (F.size r)} {i : Fin (F.size s)}
    {e : F.Col} (h : e ∈ F.pentagonEdges r j) (h' : e ∈ F.pentagonEdges s i) : r = s := by
  classical
  by_contra hrs
  rcases (F.pentagon_mem_iff _ _ _).mp h with h | h | h | h | h <;>
    rw [h] at h' <;> simp [F.pentagon_mem_iff, aux, hrs] at h'

theorem central_pentagon_intersection (r s : R) (j : Fin (F.size s)) (e : F.Col) :
    e ∈ F.centralEdges r ∧ e ∈ F.pentagonEdges s j ↔ r = s ∧ e = F.aux s j 3 := by
  classical
  constructor
  · rintro ⟨hc, hp⟩
    rcases (F.pentagon_mem_iff _ _ _).mp hp with h | h | h | h | h <;>
      rw [h] at hc <;> simp only [F.aux_mem_central] at hc
    all_goals try exact ⟨hc.1.symm, h⟩
    all_goals rcases hc with ⟨_, hc⟩; cases hc
  · rintro ⟨rfl, rfl⟩
    exact ⟨(F.aux_mem_central _ _ _ _).mpr ⟨rfl, rfl⟩,
      (F.pentagon_mem_iff _ _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩

theorem next_ne_prev (r : R) (hlen : 3 ≤ F.size r) (j : Fin (F.size r)) :
    finRotate (F.size r) j ≠ (finRotate (F.size r)).symm j := by
  classical
  intro h
  have hh := (F.centralCycle r hlen).next_next_ne_self j
  change finRotate (F.size r) (finRotate (F.size r) j) ≠ j at hh
  exact hh (by simpa only [Equiv.apply_symm_apply] using congrArg (finRotate (F.size r)) h)

theorem pentagon_intersection_cases (r : R) (j i : Fin (F.size r)) (hji : j ≠ i)
    (e : F.Col) (he : e ∈ F.pentagonEdges r j) (hi : e ∈ F.pentagonEdges r i) :
    (e = F.aux r j 2 ∧ i = finRotate (F.size r) j) ∨
      (e = F.aux r ((finRotate (F.size r)).symm j) 2 ∧ i = (finRotate (F.size r)).symm j) := by
  classical
  rcases (F.pentagon_mem_iff _ _ _).mp he with he | he | he | he | he
  · rw [he] at hi
    have hh := (F.a_mem_pentagon r r j i).mp hi
    have : i = j := by simpa using hh
    exact (hji this.symm).elim
  · rw [he] at hi
    simp [F.pentagon_mem_iff, aux, hji] at hi
  · rw [he, F.c_mem_pentagon] at hi
    rcases hi with hi | hi
    · exact (hji hi).elim
    · exact Or.inl ⟨he, ((finRotate (F.size r)).eq_symm_apply.mp hi).symm⟩
  · rw [he] at hi
    simp [F.pentagon_mem_iff, aux, hji] at hi
  · rw [he, F.c_mem_pentagon] at hi
    rcases hi with hi | hi
    · exact Or.inr ⟨he, hi.symm⟩
    · exact (hji ((finRotate (F.size r)).symm.injective hi)).elim

theorem pentagon_intersection_unique (r : R) (hlen : 3 ≤ F.size r)
    (j i : Fin (F.size r)) (hji : j ≠ i) {e f : F.Col}
    (he : e ∈ F.pentagonEdges r j) (hei : e ∈ F.pentagonEdges r i)
    (hf : f ∈ F.pentagonEdges r j) (hfi : f ∈ F.pentagonEdges r i) : e = f := by
  classical
  rcases F.pentagon_intersection_cases r j i hji e he hei with ⟨he, hi⟩ | ⟨he, hi⟩ <;>
    rcases F.pentagon_intersection_cases r j i hji f hf hfi with ⟨hf, hi'⟩ | ⟨hf, hi'⟩
  · exact he.trans hf.symm
  · exact (F.next_ne_prev r hlen j (hi.symm.trans hi')).elim
  · exact (F.next_ne_prev r hlen j (hi'.symm.trans hi)).elim
  · exact he.trans hf.symm

end ThomGame.Wheel.Family
