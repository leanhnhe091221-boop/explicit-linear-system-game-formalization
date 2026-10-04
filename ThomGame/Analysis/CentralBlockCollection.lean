module

public import ThomGame.Analysis.RelatorCollectionTools

/-! Collecting correction blocks by symbolic list induction. -/

@[expose] public section
namespace ThomGame.Analysis.RelatorEquality

variable {G Z : Type*} [Group G] [AddCommGroup Z] {rels : Set G}

theorem cross_list_right (C : Z → G) (hzero : C 0 = 1) (P Q M : ℕ)
    (hadd : ∀ z z', RelatorEquality rels (C z * C z') (C (z + z')) P)
    (u : G) (l : List G) (correction : G → Z)
    (hcross : ∀ v ∈ l, RelatorEquality rels (u * v) (C (correction v) * v * u) M)
    (hcomm : ∀ v ∈ l, ∀ z, RelatorEquality rels (v * C z) (C z * v) Q) :
    RelatorEquality rels (u * l.prod)
      (C ((l.map correction).sum) * l.prod * u) (l.length * (M + Q + P)) := by
  induction l with
  | nil => simpa [hzero] using refl (rels := rels) u
  | cons v l ih =>
    have hi := ih (fun w hw => hcross w (List.mem_cons_of_mem _ hw))
      (fun w hw => hcomm w (List.mem_cons_of_mem _ hw))
    have h₁ := (hcross v List.mem_cons_self).mul_right l.prod
    have h₂ := (hi.mul_left v).mul_left (C (correction v))
    have h₂' : RelatorEquality rels (C (correction v) * v * u * l.prod)
        (C (correction v) * v * (C ((l.map correction).sum) * l.prod * u))
        (l.length * (M + Q + P)) := by simpa only [mul_assoc] using h₂
    have h₃ := (((hcomm v List.mem_cons_self ((l.map correction).sum)).mul_left
      (C (correction v))).mul_right l.prod).mul_right u
    have h₃' : RelatorEquality rels
        (C (correction v) * v * (C ((l.map correction).sum) * l.prod * u))
        (C (correction v) * C ((l.map correction).sum) * v * l.prod * u) Q := by
      simpa only [mul_assoc] using h₃
    have h₄ := ((hadd (correction v) ((l.map correction).sum)).mul_right v).mul_right l.prod
    have h₄' := h₄.mul_right u
    have ht := ((h₁.trans h₂').trans h₃').trans h₄'
    convert ht using 1 <;> simp [List.length_cons, Nat.add_mul, mul_assoc] <;> ring

theorem cross_list_left (C : Z → G) (hzero : C 0 = 1) (P Q M : ℕ)
    (hadd : ∀ z z', RelatorEquality rels (C z * C z') (C (z + z')) P)
    (l : List G) (v : G) (correction : G → Z)
    (hcross : ∀ u ∈ l, RelatorEquality rels (u * v) (C (correction u) * v * u) M)
    (hcomm : ∀ u ∈ l, ∀ z, RelatorEquality rels (u * C z) (C z * u) Q) :
    RelatorEquality rels (l.prod * v)
      (C ((l.map correction).sum) * v * l.prod) (l.length * (M + Q + P)) := by
  induction l with
  | nil => simpa [hzero] using refl (rels := rels) v
  | cons u l ih =>
    have hi := ih (fun w hw => hcross w (List.mem_cons_of_mem _ hw))
      (fun w hw => hcomm w (List.mem_cons_of_mem _ hw))
    have h₁ := hi.mul_left u
    have h₂ := ((hcomm u List.mem_cons_self ((l.map correction).sum)).mul_right v).mul_right l.prod
    have h₂' : RelatorEquality rels (u * (C ((l.map correction).sum) * v * l.prod))
        (C ((l.map correction).sum) * u * v * l.prod) Q := by
      simpa only [mul_assoc] using h₂
    have h₃ := ((hcross u List.mem_cons_self).mul_left (C ((l.map correction).sum))).mul_right l.prod
    have h₃' : RelatorEquality rels (C ((l.map correction).sum) * u * v * l.prod)
        ((C ((l.map correction).sum) * C (correction u)) * v * (u * l.prod)) M := by
      simpa only [mul_assoc] using h₃
    have h₄ := ((hadd ((l.map correction).sum) (correction u)).mul_right v).mul_right (u * l.prod)
    have ht := ((h₁.trans h₂').trans h₃').trans h₄
    convert ht using 1 <;> simp [List.length_cons, Nat.add_mul, mul_assoc, add_comm] <;> ring

theorem cross_indices_right {I : Type*}
    (C : Z → G) (hzero : C 0 = 1) (P Q M : ℕ)
    (hadd : ∀ z z', RelatorEquality rels (C z * C z') (C (z + z')) P)
    (u : G) (values : I → G) (l : List I) (correction : I → Z)
    (hcross : ∀ v ∈ l, RelatorEquality rels (u * values v) (C (correction v) * values v * u) M)
    (hcomm : ∀ v ∈ l, ∀ z, RelatorEquality rels (values v * C z) (C z * values v) Q) :
    RelatorEquality rels (u * (l.map values).prod)
      (C ((l.map correction).sum) * (l.map values).prod * u) (l.length * (M + Q + P)) := by
  induction l with
  | nil => simpa [hzero] using refl (rels := rels) u
  | cons v l ih =>
    have hi := ih (fun w hw => hcross w (List.mem_cons_of_mem _ hw))
      (fun w hw => hcomm w (List.mem_cons_of_mem _ hw))
    have h₁ := (hcross v List.mem_cons_self).mul_right (l.map values).prod
    have h₂ := (hi.mul_left (values v)).mul_left (C (correction v))
    have h₂' : RelatorEquality rels (C (correction v) * values v * u * (l.map values).prod)
        (C (correction v) * values v * (C ((l.map correction).sum) * (l.map values).prod * u))
        (l.length * (M + Q + P)) := by simpa only [mul_assoc] using h₂
    have h₃ := (((hcomm v List.mem_cons_self ((l.map correction).sum)).mul_left
      (C (correction v))).mul_right (l.map values).prod).mul_right u
    have h₃' : RelatorEquality rels
        (C (correction v) * values v * (C ((l.map correction).sum) * (l.map values).prod * u))
        (C (correction v) * C ((l.map correction).sum) * values v * (l.map values).prod * u) Q := by
      simpa only [mul_assoc] using h₃
    have h₄ := ((hadd (correction v) ((l.map correction).sum)).mul_right (values v)).mul_right (l.map values).prod
    have h₄' := h₄.mul_right u
    have ht := ((h₁.trans h₂').trans h₃').trans h₄'
    convert ht using 1 <;> simp [List.length_cons, Nat.add_mul, mul_assoc] <;> ring

theorem cross_indices_left {I : Type*}
    (C : Z → G) (hzero : C 0 = 1) (P Q M : ℕ)
    (hadd : ∀ z z', RelatorEquality rels (C z * C z') (C (z + z')) P)
    (values : I → G) (l : List I) (v : G) (correction : I → Z)
    (hcross : ∀ u ∈ l, RelatorEquality rels (values u * v) (C (correction u) * v * values u) M)
    (hcomm : ∀ u ∈ l, ∀ z, RelatorEquality rels (values u * C z) (C z * values u) Q) :
    RelatorEquality rels ((l.map values).prod * v)
      (C ((l.map correction).sum) * v * (l.map values).prod) (l.length * (M + Q + P)) := by
  induction l with
  | nil => simpa [hzero] using refl (rels := rels) v
  | cons u l ih =>
    have hi := ih (fun w hw => hcross w (List.mem_cons_of_mem _ hw))
      (fun w hw => hcomm w (List.mem_cons_of_mem _ hw))
    have h₁ := hi.mul_left (values u)
    have h₂ := ((hcomm u List.mem_cons_self ((l.map correction).sum)).mul_right v).mul_right (l.map values).prod
    have h₂' : RelatorEquality rels (values u * (C ((l.map correction).sum) * v * (l.map values).prod))
        (C ((l.map correction).sum) * values u * v * (l.map values).prod) Q := by
      simpa only [mul_assoc] using h₂
    have h₃ := ((hcross u List.mem_cons_self).mul_left (C ((l.map correction).sum))).mul_right (l.map values).prod
    have h₃' : RelatorEquality rels (C ((l.map correction).sum) * values u * v * (l.map values).prod)
        ((C ((l.map correction).sum) * C (correction u)) * v * (values u * (l.map values).prod)) M := by
      simpa only [mul_assoc] using h₃
    have h₄ := ((hadd ((l.map correction).sum) (correction u)).mul_right v).mul_right (values u * (l.map values).prod)
    have ht := ((h₁.trans h₂').trans h₃').trans h₄
    convert ht using 1 <;> simp [List.length_cons, Nat.add_mul, mul_assoc, add_comm] <;> ring

end ThomGame.Analysis.RelatorEquality
