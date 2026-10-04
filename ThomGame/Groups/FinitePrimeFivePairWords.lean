module

public import ThomGame.Groups.FinitePrimeFivePair
public import ThomGame.Finite.Words
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Linarith

/-! Short explicit words for the three prime-five coordinate blocks. -/

@[expose] public section
namespace ThomGame.FinitePrimeFivePair

open scoped BigOperators

variable {r : ℕ}

abbrev Alphabet (r : ℕ) := Bool × Fin r

def a (i : Fin r) : FinitePrimeFivePair r := leftVector (Pi.single i 1)
def b (i : Fin r) : FinitePrimeFivePair r := rightVector (Pi.single i 1)
def c (i j : Fin r) : FinitePrimeFivePair r := centerVector (Pi.single i (Pi.single j 1))

def generator : Alphabet r → FinitePrimeFivePair r
  | (false, i) => a i
  | (true, i) => b i

def aWord (i : Fin r) : Word (Alphabet r) := Word.generator (false, i)
def bWord (i : Fin r) : Word (Alphabet r) := Word.generator (true, i)
def cWord (i j : Fin r) : Word (Alphabet r) := Word.commutator (aWord i) (bWord j)

@[simp] theorem eval_aWord (i : Fin r) : Word.eval generator (aWord i) = a i := by
  simp [aWord, generator]
@[simp] theorem eval_bWord (i : Fin r) : Word.eval generator (bWord i) = b i := by
  simp [bWord, generator]
@[simp] theorem eval_cWord (i j : Fin r) : Word.eval generator (cWord i j) = c i j := by
  rw [cWord, Word.eval_commutator, eval_aWord, eval_bWord]
  rw [a, b, commutator_vectors]
  apply congrArg centerVector
  ext k l
  by_cases hk : k = i <;> by_cases hl : l = j <;> simp [c, Pi.single_apply, hk, hl]

def repeatWord {A : Type*} (w : Word A) (n : ℕ) : Word A := (List.replicate n w).flatten

theorem eval_repeatWord {A G : Type*} [Group G] (f : A → G) (w : Word A) (n : ℕ) :
    Word.eval f (repeatWord w n) = Word.eval f w ^ n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simpa [repeatWord, List.replicate_succ, Word.eval_append, pow_succ', ih]
      using congrArg (fun g => Word.eval f w * g) ih

@[simp] theorem length_repeatWord {A : Type*} (w : Word A) (n : ℕ) :
    (repeatWord w n).length = n * w.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, List.replicate_succ, Nat.succ_mul, Nat.add_comm]

def vectorWord {I A : Type*} (indices : List I) (w : I → Word A) (α : I → ZMod 5) : Word A :=
  indices.flatMap (fun i => repeatWord (w i) (α i).val)

theorem length_vectorWord_le {I A : Type*} (indices : List I) (w : I → Word A)
    (α : I → ZMod 5) (L : ℕ) (hw : ∀ i, (w i).length ≤ L) :
    (vectorWord indices w α).length ≤ indices.length * (4 * L) := by
  induction indices with
  | nil => simp [vectorWord]
  | cons i indices ih =>
    have hi : (α i).val ≤ 4 := by have := (α i).val_lt; omega
    have hl := Nat.mul_le_mul hi (hw i)
    simp only [vectorWord, List.flatMap_cons, List.length_append, length_repeatWord,
      List.length_cons] at ih ⊢
    nlinarith

theorem eval_vectorWord {I A G : Type*} [Group G] (f : A → G)
    (indices : List I) (w : I → Word A) (α : I → ZMod 5) :
    Word.eval f (vectorWord indices w α) =
      (indices.map (fun i => Word.eval f (w i) ^ (α i).val)).prod := by
  induction indices with
  | nil => simp [vectorWord]
  | cons i indices ih =>
    simp only [vectorWord, List.flatMap_cons, Word.eval_append, eval_repeatWord,
      List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

theorem leftVector_pow (α : Fin r → ZMod 5) (n : ℕ) :
    leftVector α ^ n = leftVector (n • α) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← leftVector_add, succ_nsmul]

theorem rightVector_pow (α : Fin r → ZMod 5) (n : ℕ) :
    rightVector α ^ n = rightVector (n • α) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← rightVector_add, succ_nsmul]

theorem centerVector_pow (α : Fin r → Fin r → ZMod 5) (n : ℕ) :
    centerVector α ^ n = centerVector (n • α) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← centerVector_add, succ_nsmul]

theorem leftVector_list_sum (l : List (Fin r → ZMod 5)) :
    leftVector l.sum = (l.map leftVector).prod := by
  induction l with
  | nil => simp
  | cons α l ih => simp [leftVector_add, ih]

theorem rightVector_list_sum (l : List (Fin r → ZMod 5)) :
    rightVector l.sum = (l.map rightVector).prod := by
  induction l with
  | nil => simp
  | cons α l ih => simp [rightVector_add, ih]

theorem centerVector_list_sum (l : List (Fin r → Fin r → ZMod 5)) :
    centerVector l.sum = (l.map centerVector).prod := by
  induction l with
  | nil => simp
  | cons α l ih => simp [centerVector_add, ih]

theorem coefficient_nsmul_single (i : Fin r) (z : ZMod 5) :
    (z.val • Pi.single i (1 : ZMod 5) : Fin r → ZMod 5) = Pi.single i z := by
  ext j
  by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem coefficient_nsmul_double_single (i j : Fin r) (z : ZMod 5) :
    (z.val • Pi.single i (Pi.single j (1 : ZMod 5)) : Fin r → Fin r → ZMod 5) =
      Pi.single i (Pi.single j z) := by
  ext k l
  by_cases h : k = i <;> by_cases h' : l = j <;> simp [Pi.single_apply, h, h']

theorem eval_left_block (α : Fin r → ZMod 5) :
    Word.eval generator (vectorWord (List.finRange r) aWord α) = leftVector α := by
  rw [eval_vectorWord]
  simp only [eval_aWord, a, leftVector_pow, coefficient_nsmul_single]
  have he := leftVector_list_sum ((List.finRange r).map (fun i => Pi.single i (α i)))
  simp only [List.map_map, Function.comp_def] at he
  rw [← he]
  congr 1
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  ext j
  simp [Finset.sum_apply, Pi.single_apply, eq_comm]

theorem eval_right_block (β : Fin r → ZMod 5) :
    Word.eval generator (vectorWord (List.finRange r) bWord β) = rightVector β := by
  rw [eval_vectorWord]
  simp only [eval_bWord, b, rightVector_pow, coefficient_nsmul_single]
  have he := rightVector_list_sum ((List.finRange r).map (fun i => Pi.single i (β i)))
  simp only [List.map_map, Function.comp_def] at he
  rw [← he]
  congr 1
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  ext j
  simp [Finset.sum_apply, Pi.single_apply, eq_comm]

theorem eval_center_block (γ : Fin r → Fin r → ZMod 5) :
    Word.eval generator (vectorWord ((List.finRange r).product (List.finRange r))
      (fun p => cWord p.1 p.2) (fun p => γ p.1 p.2)) = centerVector γ := by
  rw [eval_vectorWord]
  simp only [eval_cWord, c, centerVector_pow, coefficient_nsmul_double_single]
  have he := centerVector_list_sum
    (((List.finRange r).product (List.finRange r)).map (fun p => Pi.single p.1 (Pi.single p.2 (γ p.1 p.2))))
  simp only [List.map_map, Function.comp_def] at he
  rw [← he]
  congr 1
  have hsum (xs : List (Fin r)) (f : Fin r → List (Fin r → Fin r → ZMod 5)) :
      (xs.flatMap f).sum = (xs.map (fun i => (f i).sum)).sum := by
    induction xs with
    | nil => simp
    | cons i xs ih => simp [ih]
  simp only [List.product, List.map_flatMap, List.map_map, Function.comp_def]
  rw [hsum, ← List.ofFn_eq_map, List.sum_ofFn]
  ext i j
  simp only [← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_apply]
  simp only [Pi.single_apply, ite_apply, Pi.zero_apply]
  simp [eq_comm]

def canonicalWord (g : FinitePrimeFivePair r) : Word (Alphabet r) :=
  vectorWord (List.finRange r) aWord g.left ++
    vectorWord (List.finRange r) bWord g.right ++
      vectorWord ((List.finRange r).product (List.finRange r))
        (fun p => cWord p.1 p.2) (fun p => g.central p.1 p.2)

theorem eval_canonicalWord (g : FinitePrimeFivePair r) : Word.eval generator (canonicalWord g) = g := by
  simp only [canonicalWord, Word.eval_append, eval_left_block, eval_right_block, eval_center_block]
  exact canonical_factors g

theorem canonicalWord_length (g : FinitePrimeFivePair r) :
    (canonicalWord g).length ≤ 8 * r + 16 * r ^ 2 := by
  have ha := length_vectorWord_le (List.finRange r) aWord g.left 1 (by intro i; rfl)
  have hb := length_vectorWord_le (List.finRange r) bWord g.right 1 (by intro i; rfl)
  have hc := length_vectorWord_le ((List.finRange r).product (List.finRange r))
    (fun p => cWord p.1 p.2) (fun p => g.central p.1 p.2) 4 (by intro i; rfl)
  have hp : ((List.finRange r).product (List.finRange r)).length = r * r := by
    change ((List.finRange r) ×ˢ (List.finRange r)).length = r * r
    rw [List.length_product, List.length_finRange]
  simp only [List.length_finRange, hp] at ha hb hc
  simp only [canonicalWord, List.length_append]
  nlinarith

theorem canonicalWord_length_le_840 (hr : r ≤ 7) (g : FinitePrimeFivePair r) :
    (canonicalWord g).length ≤ 840 := by
  have h := canonicalWord_length g
  nlinarith

end ThomGame.FinitePrimeFivePair
