module

public import ThomGame.Analysis.CentralBlockCollection
public import ThomGame.Groups.FinitePrimeFivePairSection

/-! Quantitative collection for adjacent prime-five root groups. -/

@[expose] public section
namespace ThomGame.Analysis

open RelatorEquality

variable {G : Type*} [Group G] {r : ℕ} {rels : Set G}

def pairCommutator (a b : Fin r → G) (p : Fin r × Fin r) : G :=
  a p.1 * b p.2 * (a p.1)⁻¹ * (b p.2)⁻¹

structure PairCollectionRelations (rels : Set G) (a b : Fin r → G) : Prop where
  a_fifth : ∀ i, RelatorEquality rels (a i ^ 5) 1 1
  b_fifth : ∀ i, RelatorEquality rels (b i ^ 5) 1 1
  aa : ∀ i j, RelatorEquality rels (a i * a j) (a j * a i) 1
  bb : ∀ i j, RelatorEquality rels (b i * b j) (b j * b i) 1
  ca : ∀ p i, RelatorEquality rels (pairCommutator a b p * a i) (a i * pairCommutator a b p) 1
  cb : ∀ p i, RelatorEquality rels (pairCommutator a b p * b i) (b i * pairCommutator a b p) 1

namespace PairCollectionRelations

variable {a b : Fin r → G} (h : PairCollectionRelations rels a b)

def indices (r : ℕ) : List (Fin r × Fin r) := (List.finRange r).product (List.finRange r)

@[simp] theorem length_indices : (indices r).length = r * r := by
  change ((List.finRange r) ×ˢ (List.finRange r)).length = _
  rw [List.length_product, List.length_finRange]

theorem indices_nodup : (indices r).Nodup :=
  List.Nodup.product (List.nodup_finRange r) (List.nodup_finRange r)

@[simp] theorem mem_indices (p : Fin r × Fin r) : p ∈ indices r := by
  rcases p with ⟨i,j⟩
  exact List.mem_product.mpr ⟨List.mem_finRange i, List.mem_finRange j⟩

def A (a : Fin r → G) (α : Fin r → ZMod 5) := blockProduct a (List.finRange r) α
def C (a b : Fin r → G) (γ : Fin r × Fin r → ZMod 5) :=
  blockProduct (pairCommutator a b) (indices r) γ

@[simp] theorem C_zero : C a b 0 = 1 := blockProduct_zero _ _

theorem C_single (p : Fin r × Fin r) (z : ZMod 5) :
    C a b (Pi.single p z) = pairCommutator a b p ^ z.val :=
  blockProduct_single _ _ indices_nodup _ (mem_indices _) _

include h

theorem cc (p q : Fin r × Fin r) :
    RelatorEquality rels (pairCommutator a b p * pairCommutator a b q)
      (pairCommutator a b q * pairCommutator a b p) 4 := by
  have hh := commute_prod_right (pairCommutator a b p)
    [a q.1, b q.2, (a q.1)⁻¹, (b q.2)⁻¹] (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact h.ca p q.1
      · exact h.cb p q.2
      · exact (h.ca p q.1).commute_inv_right
      · exact (h.cb p q.2).commute_inv_right)
  simpa only [List.prod_cons, List.prod_nil, mul_one, List.length_cons,
    List.length_nil, Nat.mul_one, pairCommutator, mul_assoc] using hh

theorem c_fifth (p : Fin r × Fin r) :
    RelatorEquality rels (pairCommutator a b p ^ 5) 1 27 := by
  exact commutator_pow_five (a p.1) (b p.2) (h.ca p p.1).symm (h.a_fifth p.1)

theorem A_add (hr : r ≤ 7) (α β : Fin r → ZMod 5) :
    RelatorEquality rels (A a α * A a β) (A a (α + β)) 1000 := by
  apply (blockProduct_add a (List.finRange r) α β 1 1 h.aa h.a_fifth).mono
  simp only [List.length_finRange]
  nlinarith

theorem B_add (hr : r ≤ 7) (α β : Fin r → ZMod 5) :
    RelatorEquality rels (A b α * A b β) (A b (α + β)) 1000 := by
  apply (blockProduct_add b (List.finRange r) α β 1 1 h.bb h.b_fifth).mono
  simp only [List.length_finRange]
  nlinarith

theorem C_add (hr : r ≤ 7) (γ γ' : Fin r × Fin r → ZMod 5) :
    RelatorEquality rels (C a b γ * C a b γ') (C a b (γ + γ')) 1000000 := by
  apply (blockProduct_add (pairCommutator a b) (indices r) γ γ' 4 27 h.cc h.c_fifth).mono
  rw [length_indices]
  have hh : r * r ≤ 49 := by nlinarith
  nlinarith

theorem C_commutes_power (hr : r ≤ 7) (u : G)
    (hu : ∀ p, RelatorEquality rels (pairCommutator a b p * u) (u * pairCommutator a b p) 1)
    (γ : Fin r × Fin r → ZMod 5) (z : ZMod 5) :
    RelatorEquality rels (C a b γ * u ^ z.val) (u ^ z.val * C a b γ) 1000 := by
  have hh := commute_prod_left ((indices r).map (fun p => pairCommutator a b p ^ (γ p).val))
    (u ^ z.val) (N := 16) (fun v hv => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv
      apply (commute_powers _ _ (hu p) (γ p).val z.val).mono
      have h₁ : (γ p).val ≤ 4 := by have := (γ p).val_lt; omega
      have h₂ : z.val ≤ 4 := by have := z.val_lt; omega
      nlinarith)
  apply hh.mono
  simp only [List.length_map, length_indices]
  nlinarith

theorem C_commutes_A (hr : r ≤ 7) (γ : Fin r × Fin r → ZMod 5) (α : Fin r → ZMod 5) :
    RelatorEquality rels (C a b γ * A a α) (A a α * C a b γ) 10000 := by
  have hh := commute_prod_right (C a b γ) ((List.finRange r).map (fun i => a i ^ (α i).val))
    (N := 1000) (fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact h.C_commutes_power hr (a i) (fun p => h.ca p i) γ (α i))
  apply hh.mono
  simp only [List.length_map, List.length_finRange]
  omega

theorem C_commutes_B (hr : r ≤ 7) (γ : Fin r × Fin r → ZMod 5) (β : Fin r → ZMod 5) :
    RelatorEquality rels (C a b γ * A b β) (A b β * C a b γ) 10000 := by
  have hh := commute_prod_right (C a b γ) ((List.finRange r).map (fun i => b i ^ (β i).val))
    (N := 1000) (fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact h.C_commutes_power hr (b i) (fun p => h.cb p i) γ (β i))
  apply hh.mono
  simp only [List.length_map, List.length_finRange]
  omega

theorem cross_powers (hr : r ≤ 7) (i j : Fin r) (α β : ZMod 5) :
    RelatorEquality rels (b j ^ β.val * a i ^ α.val)
      (C a b (Pi.single (i,j) (-(α * β))) * a i ^ α.val * b j ^ β.val) 1000 := by
  let c := pairCommutator a b (i,j)
  have he : b j * a i = c⁻¹ * a i * b j := by dsimp [c, pairCommutator]; group
  have hbc : RelatorEquality rels (b j * c⁻¹) (c⁻¹ * b j) 1 :=
    (h.cb (i,j) j).symm.commute_inv_right
  have hac : RelatorEquality rels (a i * c⁻¹) (c⁻¹ * a i) 1 :=
    (h.ca (i,j) i).symm.commute_inv_right
  have h₁ := root_pow_left (b j) (a i) c⁻¹ (of_eq he) hbc β.val
  have h₂ := root_pow_right (b j ^ β.val) (a i) (c⁻¹ ^ β.val) h₁
    (by simpa only [pow_one, Nat.one_mul, Nat.mul_one] using
      commute_powers (a i) c⁻¹ hac 1 β.val) α.val
  have hreduce := pow_mod_five c (h.c_fifth (i,j)) (α.val * β.val)
  have hreduce' : RelatorEquality rels (c ^ (α.val * β.val)) (c ^ (α * β).val)
      ((α.val * β.val / 5) * 27) := by simpa only [ZMod.val_mul] using hreduce
  have hneg := hreduce'.inv.trans (power_zmod_neg c (h.c_fifth (i,j)) (α * β))
  have heq : (c⁻¹ ^ β.val) ^ α.val = (c ^ (α.val * β.val))⁻¹ := by
    rw [← inv_pow, ← pow_mul, Nat.mul_comm]
  rw [heq] at h₂
  have ht := h₂.trans ((hneg.mul_right (a i ^ α.val)).mul_right (b j ^ β.val))
  rw [C_single]
  apply ht.mono
  have ha : α.val ≤ 4 := by have := α.val_lt; omega
  have hb : β.val ≤ 4 := by have := β.val_lt; omega
  have hp : α.val * β.val ≤ 16 := by nlinarith
  have hm : α.val * β.val / 5 ≤ 3 := by omega
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.one_mul]
  nlinarith [Nat.mul_le_mul ha hb]

theorem cross_blocks (hr : r ≤ 7) (α β : Fin r → ZMod 5) :
    RelatorEquality rels (A b β * A a α)
      (C a b (fun p => -(α p.1 * β p.2)) * A a α * A b β) 100000000 := by
  let correction (j : Fin r) : Fin r × Fin r → ZMod 5 :=
    ((List.finRange r).map (fun i => Pi.single (i,j) (-(α i * β j)))).sum
  have hrght (j : Fin r) : RelatorEquality rels (b j ^ (β j).val * A a α)
      (C a b (correction j) * A a α * b j ^ (β j).val) 10000000 := by
    have ht := cross_indices_right (C a b) C_zero 1000000 1000 1000 (h.C_add hr)
      (b j ^ (β j).val) (fun i => a i ^ (α i).val) (List.finRange r)
      (fun i => Pi.single (i,j) (-(α i * β j)))
      (fun i _ => h.cross_powers hr i j (α i) (β j))
      (fun i _ γ => (h.C_commutes_power hr (a i) (fun p => h.ca p i) γ (α i)).symm)
    apply ht.mono
    simp only [List.length_finRange]
    omega
  have ht := cross_indices_left (C a b) C_zero 1000000 1000 10000000 (h.C_add hr)
    (fun j => b j ^ (β j).val) (List.finRange r) (A a α) correction
    (fun j _ => hrght j)
    (fun j _ γ => (h.C_commutes_power hr (b j) (fun p => h.cb p j) γ (β j)).symm)
  have hsum : ((List.finRange r).map correction).sum = (fun p => -(α p.1 * β p.2)) := by
    ext p
    simp only [correction, ← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_apply]
    simp [Pi.single_apply, Prod.ext_iff, ite_and]
  rw [hsum] at ht
  apply ht.mono
  simp only [List.length_finRange]
  omega

def normal (a b : Fin r → G) (g : FinitePrimeFivePair r) : G :=
  A a g.left * A b g.right * C a b (fun p => g.central p.1 p.2)

@[simp] theorem normal_one : normal a b (1 : FinitePrimeFivePair r) = 1 := by
  simp [normal, A, C, blockProduct]

theorem normal_mul (hr : r ≤ 7) (g k : FinitePrimeFivePair r) :
    RelatorEquality rels (normal a b g * normal a b k) (normal a b (g * k)) 1000000000 := by
  let γ : Fin r × Fin r → ZMod 5 := fun p => g.central p.1 p.2
  let γ' : Fin r × Fin r → ZMod 5 := fun p => k.central p.1 p.2
  let κ : Fin r × Fin r → ZMod 5 := fun p => -(k.left p.1 * g.right p.2)
  have hmove : RelatorEquality rels (C a b γ * (A a k.left * A b k.right))
      ((A a k.left * A b k.right) * C a b γ) 20000 := by
    have h₁ := (h.C_commutes_A hr γ k.left).mul_right (A b k.right)
    have h₂ := (h.C_commutes_B hr γ k.right).mul_left (A a k.left)
    have h₂' : RelatorEquality rels (A a k.left * C a b γ * A b k.right)
        (A a k.left * A b k.right * C a b γ) 10000 := by
      simpa only [mul_assoc] using h₂
    simpa only [mul_assoc] using h₁.trans h₂'
  have h₁ := (hmove.mul_left (A a g.left * A b g.right)).mul_right (C a b γ')
  have h₁' : RelatorEquality rels (normal a b g * normal a b k)
      (A a g.left * (A b g.right * A a k.left) * A b k.right * C a b γ * C a b γ') 20000 := by
    simpa only [normal, γ, γ', mul_assoc] using h₁
  have h₂ := ((((h.cross_blocks hr k.left g.right).mul_left (A a g.left)).mul_right
    (A b k.right)).mul_right (C a b γ)).mul_right (C a b γ')
  have h₂' : RelatorEquality rels
      (A a g.left * (A b g.right * A a k.left) * A b k.right * C a b γ * C a b γ')
      (A a g.left * (C a b κ * (A a k.left * A b g.right * A b k.right)) * C a b γ * C a b γ')
      100000000 := by simpa only [κ, mul_assoc] using h₂
  have hcm : RelatorEquality rels
      (C a b κ * (A a k.left * A b g.right * A b k.right))
      ((A a k.left * A b g.right * A b k.right) * C a b κ) 30000 := by
    have hc := commute_prod_right (C a b κ) [A a k.left, A b g.right, A b k.right]
      (N := 10000) (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact h.C_commutes_A hr κ k.left
        · exact h.C_commutes_B hr κ g.right
        · exact h.C_commutes_B hr κ k.right)
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.length_cons,
      List.length_nil, mul_assoc] using hc
  have h₃ := ((hcm.mul_left (A a g.left)).mul_right (C a b γ)).mul_right (C a b γ')
  have h₃' : RelatorEquality rels
      (A a g.left * (C a b κ * (A a k.left * A b g.right * A b k.right)) * C a b γ * C a b γ')
      ((A a g.left * A a k.left) * (A b g.right * A b k.right) *
        (C a b κ * C a b γ * C a b γ')) 30000 := by
    simpa only [mul_assoc] using h₃
  have hC := ((h.C_add hr κ γ).mul_right (C a b γ')).trans (h.C_add hr (κ + γ) γ')
  have h₄ := ((h.A_add hr g.left k.left).mul (h.B_add hr g.right k.right)).mul hC
  have he : normal a b (g * k) =
      A a (g.left + k.left) * A b (g.right + k.right) * C a b (κ + γ + γ') := by
    simp only [normal, FinitePrimeFivePair.mul_left, FinitePrimeFivePair.mul_right]
    congr 1
    apply congrArg (C a b)
    funext p
    simp [κ, γ, γ', sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [he]
  exact (((h₁'.trans h₂').trans h₃').trans h₄).mono (by decide)

end PairCollectionRelations
end ThomGame.Analysis
