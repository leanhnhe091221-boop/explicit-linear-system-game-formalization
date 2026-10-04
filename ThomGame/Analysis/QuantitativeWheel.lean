module

public import ThomGame.Analysis.RelatorAreaBounds
public import ThomGame.Groups.WheelProduct

/-! Finite area bounds for the existing wheel elimination. The estimates allow
approximate involutions, and retain explicit integer constants throughout. -/

@[expose] public section
namespace ThomGame.Analysis.RelatorArea

variable {G : Type*} [Group G] {rels : Set G}

theorem inverse_of_square {x : G} {n : ℕ} (hx : RelatorArea rels (x * x) n) :
    RelatorArea rels (x⁻¹ * x⁻¹) n := by
  simpa only [mul_inv_rev] using hx.inv

theorem solve_first_area {x y z q : G}
    (h : RelatorArea rels ((x * y * z) * q⁻¹) 1)
    (hy : RelatorArea rels (y * y) 1) (hz : RelatorArea rels (z * z) 1)
    (hc : RelatorArea rels ((y * z) * (z * y)⁻¹) 1) :
    RelatorArea rels (x * (q * y * z)⁻¹) 4 := by
  have h₁ : RelatorArea rels (x * (q * z⁻¹ * y⁻¹)⁻¹) 1 := by
    convert h.mul_right (z⁻¹ * y⁻¹) using 1 <;> group
  have h₂ : RelatorArea rels
      ((q * z⁻¹ * y⁻¹) * (q * z * y⁻¹)⁻¹) 1 :=
    (hz.inverse_of_square.mul_left q).mul_right y⁻¹
  have h₃ : RelatorArea rels
      ((q * z * y⁻¹) * (q * z * y)⁻¹) 1 := hy.inverse_of_square.mul_left (q * z)
  have h₄ : RelatorArea rels ((q * z * y) * (q * y * z)⁻¹) 1 := by
    simpa only [mul_assoc] using hc.symm.mul_left q
  exact ((h₁.trans h₂).trans h₃).trans h₄

theorem ofFn_product_area (n m : ℕ) (f g : Fin n → G)
    (h : ∀ i, RelatorArea rels (f i * (g i)⁻¹) m) :
    RelatorArea rels ((List.ofFn f).prod * ((List.ofFn g).prod)⁻¹) (n * m) := by
  induction n with
  | zero => simpa using (RelatorArea.one (rels := rels))
  | succ n ih =>
    have h₁ := (h 0).mul_right (List.ofFn (fun i : Fin n => f i.succ)).prod
    have h₂ := (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)).mul_left (g 0)
    simpa only [List.ofFn_succ, List.prod_cons, Nat.succ_mul, Nat.add_comm] using h₁.trans h₂

theorem wheel_word_area {n : ℕ} [NeZero n] (s a b c d : Fin n → G) (q : G)
    (ha : ∀ j, RelatorArea rels (a j * a j) 1)
    (hb : ∀ j, RelatorArea rels (b j * b j) 1)
    (hc : ∀ j, RelatorArea rels (c j * c j) 1)
    (hd : ∀ j, RelatorArea rels (d j * d j) 1)
    (h₁ : ∀ j, RelatorArea rels ((s j * a j * b j) * (if j = 0 then q else 1)⁻¹) 1)
    (h₂ : ∀ j, RelatorArea rels (b j * c j * a (finRotate n j)) 1)
    (h₃ : ∀ j, RelatorArea rels (c j * d j * d (finRotate n j)) 1)
    (hcomm₁ : ∀ j, RelatorArea rels ((a j * b j) * (b j * a j)⁻¹) 1)
    (hcomm₂ : ∀ j, RelatorArea rels ((c j * a (finRotate n j)) *
      (a (finRotate n j) * c j)⁻¹) 1)
    (hcomm₃ : ∀ j, RelatorArea rels ((d j * d (finRotate n j)) *
      (d (finRotate n j) * d j)⁻¹) 1) :
    RelatorArea rels ((List.ofFn s).prod * q⁻¹) (n * 14) := by
  let k (j : Fin n) := a j * d j
  have hlocal j : RelatorArea rels
      (s j * ((if j = 0 then q else 1) * (k j * (k (finRotate n j))⁻¹))⁻¹) 14 := by
    let t := if j = 0 then q else 1
    let j' := finRotate n j
    have e₁ := solve_first_area (h₁ j) (ha j) (hb j) (hcomm₁ j)
    have e₂ : RelatorArea rels (b j * (c j * a j')⁻¹) 4 := by
      simpa only [inv_one, mul_one, one_mul] using
        solve_first_area (q := (1 : G)) (by simpa only [inv_one, mul_one] using h₂ j)
          (hc j) (ha j') (hcomm₂ j)
    have e₃ : RelatorArea rels (c j * (d j * d j')⁻¹) 4 := by
      simpa only [inv_one, mul_one, one_mul] using
        solve_first_area (q := (1 : G)) (by simpa only [inv_one, mul_one] using h₃ j)
          (hd j) (hd j') (hcomm₃ j)
    have e₂' : RelatorArea rels ((t * a j * b j) * (t * a j * c j * a j')⁻¹) 4 := by
      simpa only [mul_assoc] using e₂.mul_left (t * a j)
    have e₃' : RelatorArea rels
        ((t * a j * c j * a j') * (t * a j * d j * d j' * a j')⁻¹) 4 := by
      simpa only [mul_assoc] using (e₃.mul_left (t * a j)).mul_right (a j')
    have e₄ : RelatorArea rels
        ((t * a j * d j * d j' * a j') * (t * a j * d j * (d j')⁻¹ * a j')⁻¹) 1 :=
      ((hd j').inverse_of_square.symm.mul_left (t * a j * d j)).mul_right (a j')
    have e₅ : RelatorArea rels
        ((t * a j * d j * (d j')⁻¹ * a j') *
          (t * a j * d j * (d j')⁻¹ * (a j')⁻¹)⁻¹) 1 :=
      (ha j').inverse_of_square.symm.mul_left (t * a j * d j * (d j')⁻¹)
    have he := (((e₁.trans e₂').trans e₃').trans e₄).trans e₅
    simpa only [k, j', t, mul_inv_rev, mul_assoc] using he
  have hprod := ofFn_product_area n 14 s
    (fun j => (if j = 0 then q else 1) * (k j * (k (finRotate n j))⁻¹)) hlocal
  simpa only [ofFn_first_factor, ofFn_cyclic_telescope, mul_one] using hprod

end ThomGame.Analysis.RelatorArea
