module

public import ThomGame.Finite.CyclicProducts
public import ThomGame.Finite.WheelSystem
public import ThomGame.Groups.SolutionGroup

/-!
# The relation encoded by a wagon wheel

The proof uses ordered products, so it applies to noncommutative groups.
Writing k_j = a_j d_j, the wheel equations give
s_j = (if j = 0 then q else 1) k_j k_(j+1)⁻¹.
The product telescopes to q.
-/

@[expose] public section
namespace ThomGame.Wheel

variable {G : Type*} [Group G]

theorem solve_first {x y z q : G} (h : x * y * z = q)
    (hy : y * y = 1) (hz : z * z = 1) (hc : Commute y z) : x = q * y * z := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz
  calc
    x = (x * y * z) * z⁻¹ * y⁻¹ := by group
    _ = q * y * z := by
      rw [h, hzi, hyi, mul_assoc, ← hc.eq, ← mul_assoc]

theorem group_word_product {n : Nat} [NeZero n] (s a b c d : Fin n → G) (q : G)
    (ha : ∀ j, a j * a j = 1) (hb : ∀ j, b j * b j = 1)
    (hc : ∀ j, c j * c j = 1) (hd : ∀ j, d j * d j = 1)
    (h₁ : ∀ j, s j * a j * b j = if j = 0 then q else 1)
    (h₂ : ∀ j, b j * c j * a (finRotate n j) = 1)
    (h₃ : ∀ j, c j * d j * d (finRotate n j) = 1)
    (hcomm₁ : ∀ j, Commute (a j) (b j))
    (hcomm₂ : ∀ j, Commute (c j) (a (finRotate n j)))
    (hcomm₃ : ∀ j, Commute (d j) (d (finRotate n j))) :
    (List.ofFn s).prod = q := by
  let k (j : Fin n) := a j * d j
  have hs (j : Fin n) :
      s j = (if j = 0 then q else 1) * (k j * (k (finRotate n j))⁻¹) := by
    rw [solve_first (h₁ j) (ha j) (hb j) (hcomm₁ j),
      solve_first (h₂ j) (hc j) (ha _) (hcomm₂ j),
      solve_first (h₃ j) (hd j) (hd _) (hcomm₃ j)]
    simp only [k, mul_inv_rev, inv_eq_of_mul_eq_one_left (ha (finRotate n j)),
      inv_eq_of_mul_eq_one_left (hd (finRotate n j)), one_mul, mul_assoc]
  have heq : s = fun j => (if j = 0 then q else 1) * (k j * (k (finRotate n j))⁻¹) :=
    funext hs
  rw [heq, ofFn_first_factor, ofFn_cyclic_telescope, mul_one]

namespace Family

variable {R S : Type*} (F : Family R S)

/-- The ordinary generators in a wheel satisfy its original relation in the
solution group. No collegiality or injectivity assumption is needed here. -/
theorem solution_word_product (r : R) :
    (List.ofFn (fun j => SolutionGroup.x F.system (.inl (F.letter r j)))).prod =
      if F.parity r = 1 then SolutionGroup.J F.system else 1 := by
  apply group_word_product _
    (fun j => SolutionGroup.x F.system (F.aux r j 0))
    (fun j => SolutionGroup.x F.system (F.aux r j 1))
    (fun j => SolutionGroup.x F.system (F.aux r j 2))
    (fun j => SolutionGroup.x F.system (F.aux r j 3)) _
  · intro j; exact SolutionGroup.x_sq F.system _
  · intro j; exact SolutionGroup.x_sq F.system _
  · intro j; exact SolutionGroup.x_sq F.system _
  · intro j; exact SolutionGroup.x_sq F.system _
  · intro j
    have h := SolutionGroup.row_product F.system ⟨r, j, 0⟩
    change SolutionGroup.x F.system (.inl (F.letter r j)) *
      SolutionGroup.x F.system (F.aux r j 0) * SolutionGroup.x F.system (F.aux r j 1) =
      (if (if j = 0 ∧ (0 : Fin 3) = 0 then F.parity r else 0) = 1 then
      SolutionGroup.J F.system else 1) at h
    by_cases hj : j = 0 <;> simpa [hj] using h
  · intro j
    have h := SolutionGroup.row_product F.system ⟨r, j, 1⟩
    change SolutionGroup.x F.system (F.aux r j 1) *
      SolutionGroup.x F.system (F.aux r j 2) *
      SolutionGroup.x F.system (F.aux r (finRotate (F.size r) j) 0) =
      (if (if j = 0 ∧ (1 : Fin 3) = 0 then F.parity r else 0) = 1 then
      SolutionGroup.J F.system else 1) at h
    simpa using h
  · intro j
    have h := SolutionGroup.row_product F.system ⟨r, j, 2⟩
    change SolutionGroup.x F.system (F.aux r j 2) *
      SolutionGroup.x F.system (F.aux r j 3) *
      SolutionGroup.x F.system (F.aux r (finRotate (F.size r) j) 3) =
      (if (if j = 0 ∧ (2 : Fin 3) = 0 then F.parity r else 0) = 1 then
      SolutionGroup.J F.system else 1) at h
    simpa using h
  · intro j
    exact SolutionGroup.row_commutes F.system ⟨r, j, 0⟩ 1 2
  · intro j
    exact SolutionGroup.row_commutes F.system ⟨r, j, 1⟩ 1 2
  · intro j
    exact SolutionGroup.row_commutes F.system ⟨r, j, 2⟩ 1 2

end Family
end ThomGame.Wheel
