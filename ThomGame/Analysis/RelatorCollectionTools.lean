module

public import ThomGame.Analysis.RelatorAreaCalculus
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.List.Nodup

/-! Symbolic collection tools with explicit relator-area bounds. -/

@[expose] public section
namespace ThomGame.Analysis.RelatorEquality

variable {G : Type*} [Group G] {rels : Set G} {N : ℕ}

theorem pow (u v : G) (h : RelatorEquality rels u v N) (n : ℕ) :
    RelatorEquality rels (u ^ n) (v ^ n) (n * N) := by
  induction n with
  | zero => simpa using refl (rels := rels) (1 : G)
  | succ n ih => simpa only [pow_succ, Nat.succ_mul, Nat.add_comm] using ih.mul h

theorem commute_prod_right (u : G) (l : List G)
    (h : ∀ v ∈ l, RelatorEquality rels (u * v) (v * u) N) :
    RelatorEquality rels (u * l.prod) (l.prod * u) (l.length * N) := by
  induction l with
  | nil => simpa using refl (rels := rels) u
  | cons v l ih =>
    have h₁ := (h v List.mem_cons_self).mul_right l.prod
    have h₂ := (ih (fun w hw => h w (List.mem_cons_of_mem _ hw))).mul_left v
    have h₂' : RelatorEquality rels (v * u * l.prod) (v * (l.prod * u)) (l.length * N) := by
      simpa only [mul_assoc] using h₂
    simpa only [List.prod_cons, List.length_cons, mul_assoc, Nat.add_mul, Nat.one_mul,
      Nat.add_comm] using h₁.trans h₂'

theorem commute_prod_left (l : List G) (u : G)
    (h : ∀ v ∈ l, RelatorEquality rels (v * u) (u * v) N) :
    RelatorEquality rels (l.prod * u) (u * l.prod) (l.length * N) :=
  (commute_prod_right u l (fun v hv => (h v hv).symm)).symm

theorem commute_products (l k : List G)
    (h : ∀ u ∈ l, ∀ v ∈ k, RelatorEquality rels (u * v) (v * u) N) :
    RelatorEquality rels (l.prod * k.prod) (k.prod * l.prod) (l.length * k.length * N) := by
  have hp : ∀ u ∈ l, RelatorEquality rels (u * k.prod) (k.prod * u) (k.length * N) :=
    fun u hu => commute_prod_right u k (h u hu)
  simpa only [Nat.mul_assoc] using commute_prod_left l k.prod hp

theorem commute_powers (u v : G) (h : RelatorEquality rels (u * v) (v * u) N) (m n : ℕ) :
    RelatorEquality rels (u ^ m * v ^ n) (v ^ n * u ^ m) (m * n * N) := by
  have hh := commute_products (List.replicate m u) (List.replicate n v)
    (fun u' hu v' hv => by
      have hu' := (List.mem_replicate.mp hu).2
      have hv' := (List.mem_replicate.mp hv).2
      subst u'
      subst v'
      exact h)
  simpa only [List.prod_replicate, List.length_replicate] using hh

theorem pow_mod_five_le_eight (u : G) (h : RelatorEquality rels (u ^ 5) 1 N)
    (n : ℕ) (hn : n ≤ 8) : RelatorEquality rels (u ^ n) (u ^ (n % 5)) N := by
  by_cases hsmall : n < 5
  · rw [Nat.mod_eq_of_lt hsmall]
    exact (refl _).mono (Nat.zero_le _)
  · have hle : 5 ≤ n := by omega
    have he : n = 5 + (n - 5) := by omega
    have hm : n % 5 = n - 5 := by omega
    rw [hm, he, pow_add]
    simpa only [one_mul, Nat.add_sub_cancel_left] using h.mul_right (u ^ (n - 5))

theorem powers_add_zmod_five (u : G) (h : RelatorEquality rels (u ^ 5) 1 N)
    (a b : ZMod 5) :
    RelatorEquality rels (u ^ a.val * u ^ b.val) (u ^ (a + b).val) N := by
  rw [← pow_add, ZMod.val_add]
  apply pow_mod_five_le_eight u h
  have ha := a.val_lt
  have hb := b.val_lt
  omega

def blockProduct {I : Type*} (u : I → G) (l : List I) (α : I → ZMod 5) : G :=
  (l.map (fun i => u i ^ (α i).val)).prod

@[simp] theorem blockProduct_zero {I : Type*} (u : I → G) (l : List I) :
    blockProduct u l 0 = 1 := by simp [blockProduct]

theorem blockProduct_single {I : Type*} [DecidableEq I] (u : I → G) (l : List I)
    (hl : l.Nodup) (i : I) (hi : i ∈ l) (z : ZMod 5) :
    blockProduct u l (Pi.single i z) = u i ^ z.val := by
  unfold blockProduct
  rw [List.prod_map_eq_pow_single i]
  · simp [List.count_eq_one_of_mem hl hi]
  · intro j hj _
    simp [Pi.single_apply, hj]

theorem power_zmod_neg (u : G) (hp : RelatorEquality rels (u ^ 5) 1 N) (z : ZMod 5) :
    RelatorEquality rels (u ^ z.val)⁻¹ (u ^ (-z).val) N := by
  have hh := (powers_add_zmod_five u hp z (-z)).mul_left (u ^ z.val)⁻¹
  simpa only [add_neg_cancel, ZMod.val_zero, pow_zero, inv_mul_cancel_left, mul_one]
    using hh.symm

theorem pow_mod_five (u : G) (h : RelatorEquality rels (u ^ 5) 1 N)
    (n : ℕ) : RelatorEquality rels (u ^ n) (u ^ (n % 5)) ((n / 5) * N) := by
  have he : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  have hh := (pow _ _ h (n / 5)).mul_right (u ^ (n % 5))
  rw [← pow_mul] at hh
  simpa only [← pow_add, ← he, one_pow, one_mul] using hh

theorem root_pow_left (u v c : G) {M P : ℕ}
    (h : RelatorEquality rels (u * v) (c * v * u) M)
    (hc : RelatorEquality rels (u * c) (c * u) P) (n : ℕ) :
    RelatorEquality rels (u ^ n * v) (c ^ n * v * u ^ n) (n * M + n ^ 2 * P) := by
  induction n with
  | zero => simpa using refl (rels := rels) v
  | succ n ih =>
    have h₁ := ih.mul_left u
    have h₂ := ((commute_powers u c hc 1 n).mul_right v).mul_right (u ^ n)
    have h₂' : RelatorEquality rels (u * (c ^ n * v * u ^ n))
        (c ^ n * u * v * u ^ n) (n * P) := by
      simpa only [pow_one, Nat.one_mul, mul_assoc] using h₂
    have h₃ := (h.mul_left (c ^ n)).mul_right (u ^ n)
    have h₃' : RelatorEquality rels (c ^ n * u * v * u ^ n)
        (c ^ (n + 1) * v * u ^ (n + 1)) M := by
      simpa only [pow_succ c n, pow_succ' u n, mul_assoc] using h₃
    have ht := (h₁.trans h₂').trans h₃'
    have hb : (n * M + n ^ 2 * P) + n * P + M ≤
        (n + 1) * M + (n + 1) ^ 2 * P := by nlinarith
    simpa only [pow_succ' u n, mul_assoc] using ht.mono hb

theorem root_pow_right (u v c : G) {M P : ℕ}
    (h : RelatorEquality rels (u * v) (c * v * u) M)
    (hc : RelatorEquality rels (v * c) (c * v) P) (n : ℕ) :
    RelatorEquality rels (u * v ^ n) (c ^ n * v ^ n * u) (n * M + n ^ 2 * P) := by
  induction n with
  | zero => simpa using refl (rels := rels) u
  | succ n ih =>
    have h₁ := h.mul_right (v ^ n)
    have h₂ := (ih.mul_left v).mul_left c
    have h₂' : RelatorEquality rels (c * v * u * v ^ n)
        (c * v * (c ^ n * v ^ n * u)) (n * M + n ^ 2 * P) := by
      simpa only [mul_assoc] using h₂
    have h₃ := (((commute_powers v c hc 1 n).mul_left c).mul_right (v ^ n)).mul_right u
    have h₃' : RelatorEquality rels (c * v * (c ^ n * v ^ n * u))
        (c ^ (n + 1) * v ^ (n + 1) * u) (n * P) := by
      simpa only [pow_one, Nat.one_mul, pow_succ' c n, pow_succ' v n, mul_assoc] using h₃
    have ht := (h₁.trans h₂').trans h₃'
    have hb : M + (n * M + n ^ 2 * P) + n * P ≤
        (n + 1) * M + (n + 1) ^ 2 * P := by nlinarith
    simpa only [pow_succ' v n, mul_assoc] using ht.mono hb

theorem commutator_pow_five (u v : G) {P : ℕ}
    (hc : RelatorEquality rels
      (u * (u * v * u⁻¹ * v⁻¹)) ((u * v * u⁻¹ * v⁻¹) * u) N)
    (hp : RelatorEquality rels (u ^ 5) 1 P) :
    RelatorEquality rels ((u * v * u⁻¹ * v⁻¹) ^ 5) 1 (25 * N + 2 * P) := by
  let c := u * v * u⁻¹ * v⁻¹
  have hx : u * v = c * v * u := by dsimp [c]; group
  have h := root_pow_left u v c (of_eq hx) hc 5
  have h₁ : RelatorEquality rels v (u ^ 5 * v) P := by
    simpa only [one_mul] using (hp.mul_right v).symm
  have h₂ : RelatorEquality rels (c ^ 5 * v * u ^ 5) (c ^ 5 * v) P := by
    simpa only [mul_one] using hp.mul_left (c ^ 5 * v)
  have hh := ((h₁.trans h).trans h₂).symm.mul_right v⁻¹
  simpa only [c, mul_assoc, mul_inv_cancel, mul_one, Nat.mul_zero, Nat.zero_add,
    show 5 ^ 2 = 25 from rfl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.two_mul] using hh

theorem blockProduct_add {I : Type*} (u : I → G) (l : List I) (α β : I → ZMod 5)
    (N P : ℕ)
    (hc : ∀ i j, RelatorEquality rels (u i * u j) (u j * u i) N)
    (hp : ∀ i, RelatorEquality rels (u i ^ 5) 1 P) :
    RelatorEquality rels (blockProduct u l α * blockProduct u l β)
      (blockProduct u l (α + β)) (16 * l.length ^ 2 * N + l.length * P) := by
  induction l with
  | nil => simpa [blockProduct] using refl (rels := rels) (1 : G)
  | cons i l ih =>
    have hm (j : I) : RelatorEquality rels
        (u j ^ (α j).val * u i ^ (β i).val) (u i ^ (β i).val * u j ^ (α j).val) (16 * N) := by
      apply (commute_powers (u j) (u i) (hc j i) (α j).val (β i).val).mono
      have ha : (α j).val ≤ 4 := by have := (α j).val_lt; omega
      have hb : (β i).val ≤ 4 := by have := (β i).val_lt; omega
      exact Nat.mul_le_mul_right N (by nlinarith)
    have hs := commute_prod_left (l.map (fun j => u j ^ (α j).val)) (u i ^ (β i).val)
      (fun v hv => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv; exact hm j)
    have hs' : RelatorEquality rels
        (blockProduct u (i :: l) α * blockProduct u (i :: l) β)
        ((u i ^ (α i).val * u i ^ (β i).val) * (blockProduct u l α * blockProduct u l β))
        (l.length * (16 * N)) := by
      simpa only [blockProduct, List.map_cons, List.prod_cons, List.length_map, mul_assoc]
        using (hs.mul_left (u i ^ (α i).val)).mul_right (blockProduct u l β)
    have hc' := (powers_add_zmod_five (u i) (hp i) (α i) (β i)).mul ih
    have ht := hs'.trans hc'
    have hbound : l.length * (16 * N) + (P + (16 * l.length ^ 2 * N + l.length * P)) ≤
        16 * (l.length + 1) ^ 2 * N + (l.length + 1) * P := by nlinarith
    have ht' := ht.mono hbound
    simpa only [blockProduct, List.map_cons, List.prod_cons, List.length_cons, Pi.add_apply] using ht'

end ThomGame.Analysis.RelatorEquality

