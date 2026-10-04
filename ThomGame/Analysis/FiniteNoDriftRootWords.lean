module

public import ThomGame.Analysis.FiniteNoDriftWords
public import ThomGame.Groups.FinitePrimeFivePairWords

/-! Canonical finite cyclic-root tuples. The existing lazy Markov map supplies their inverse symmetrization. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

abbrev FiniteNoDriftRootIndex (r : Nat) := Fin 3 × (Fin r → ZMod 5)

theorem finiteNoDriftRootIndex_card (r : Nat) : Fintype.card (FiniteNoDriftRootIndex r) = 3 * 5 ^ r := by
  simp [FiniteNoDriftRootIndex, Fintype.card_prod, Fintype.card_fun, ZMod.card]

def finiteNoDriftCoefficient : Fin 7 → Compressor.Coeff :=
  ![none, some (0, true), some (1, true), some (2, true),
    some (0, false), some (1, false), some (2, false)]

def finiteNoDriftPositiveCoefficient (i : Fin 4) : Compressor.Coeff :=
  finiteNoDriftCoefficient (i.castAdd 3)

def finiteNoDriftRootWord {r : Nat} (σ : Fin r → Compressor.Coeff)
    (c : Fin 3) (α : Fin r → ZMod 5) : Word Compressor.Generator :=
  FinitePrimeFivePair.vectorWord (List.finRange r) (fun i => Compressor.X (Compressor.cyclicRoot c) (σ i)) α

theorem finiteNoDriftRootWord_length {r : Nat} (σ : Fin r → Compressor.Coeff)
    (c : Fin 3) (α : Fin r → ZMod 5) : (finiteNoDriftRootWord σ c α).length ≤ 4 * r := by
  have h := FinitePrimeFivePair.length_vectorWord_le (List.finRange r)
    (fun i => Compressor.X (Compressor.cyclicRoot c) (σ i)) α 1 (by intro i; rfl)
  simpa only [finiteNoDriftRootWord, List.length_finRange, mul_one, Nat.mul_comm] using h

theorem finiteNoDriftRootWord_mem {r : Nat} (σ : Fin r → Compressor.Coeff)
    (c : Fin 3) (α : Fin r → ZMod 5) (g : Compressor.Generator) (b : Bool)
    (hm : (g, b) ∈ finiteNoDriftRootWord σ c α) :
    ∃ i, g = .inl (Compressor.cyclicRoot c, σ i) := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hm
  simp only [FinitePrimeFivePair.repeatWord, List.mem_flatten, List.mem_replicate] at hi
  obtain ⟨w, ⟨_, rfl⟩, hw⟩ := hi
  simp only [Compressor.X, Word.generator, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hw
  exact ⟨i, hw.1⟩

noncomputable def finiteNoDriftRootTuple {d r : Nat} (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) : Fin (3 * 5 ^ r) → UnitaryMatrix d := fun j =>
  let p := (Fintype.equivFinOfCardEq (finiteNoDriftRootIndex_card r)).symm j
  Word.eval f (finiteNoDriftRootWord σ p.1 p.2)

theorem finiteNoDriftRootTuple_at {d r : Nat} (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (p : FiniteNoDriftRootIndex r) :
    finiteNoDriftRootTuple f σ ((Fintype.equivFinOfCardEq (finiteNoDriftRootIndex_card r)) p) =
      Word.eval f (finiteNoDriftRootWord σ p.1 p.2) := by
  simp only [finiteNoDriftRootTuple, Equiv.symm_apply_apply]

theorem finiteNoDriftRootTuple_comm {d r : Nat} (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (X : CMatrix d) {a : ℝ} (ha : 0 ≤ a)
    (hroot : ∀ c i, finiteNoDriftComm (f (.inl (Compressor.cyclicRoot c, σ i))) X ≤ a)
    (j : Fin (3 * 5 ^ r)) : finiteNoDriftComm (finiteNoDriftRootTuple f σ j) X ≤ (4 * r : Nat) * a := by
  let p := (Fintype.equivFinOfCardEq (finiteNoDriftRootIndex_card r)).symm j
  have hw := finiteNoDrift_word_comm f (finiteNoDriftRootWord σ p.1 p.2) X (fun g b hg => by
    obtain ⟨i, rfl⟩ := finiteNoDriftRootWord_mem σ p.1 p.2 g b hg
    exact hroot p.1 i)
  exact hw.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (finiteNoDriftRootWord_length σ p.1 p.2)) ha)

theorem finiteNoDrift_vectorWord_single {I S : Type*} [DecidableEq I]
    (l : List I) (hl : l.Nodup) (w : I → Word S) (i : I) :
    FinitePrimeFivePair.vectorWord l w (Pi.single i (1 : ZMod 5)) = if i ∈ l then w i else [] := by
  induction l with
  | nil => simp [FinitePrimeFivePair.vectorWord]
  | cons x l ih =>
    have ht := hl.of_cons
    have hxnot := (List.nodup_cons.mp hl).1
    have ih' := ih ht
    change FinitePrimeFivePair.repeatWord (w x) (((Pi.single i (1 : ZMod 5)) : I → ZMod 5) x).val ++
      FinitePrimeFivePair.vectorWord l w (Pi.single i 1) = _
    rw [ih']
    by_cases hxi : x = i
    · subst x
      have hv : (1 : ZMod 5).val = 1 := by decide
      simp [FinitePrimeFivePair.repeatWord, hxnot, hv]
    · have he : (Pi.single i (1 : ZMod 5) : I → ZMod 5) x = 0 := by simp [Pi.single_apply, hxi]
      simp [he, FinitePrimeFivePair.repeatWord, Ne.symm hxi]

theorem finiteNoDriftRootWord_single {r : Nat} (σ : Fin r → Compressor.Coeff)
    (c : Fin 3) (i : Fin r) :
    finiteNoDriftRootWord σ c (Pi.single i 1) = Compressor.X (Compressor.cyclicRoot c) (σ i) := by
  exact (finiteNoDrift_vectorWord_single (List.finRange r) (List.nodup_finRange r) _ i).trans
    (if_pos (List.mem_finRange i))

theorem finiteNoDriftRootTuple_generator {d r : Nat} (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (c : Fin 3) (i : Fin r) :
    ∃ j, finiteNoDriftRootTuple f σ j = f (.inl (Compressor.cyclicRoot c, σ i)) := by
  refine ⟨(Fintype.equivFinOfCardEq (finiteNoDriftRootIndex_card r)) (c, Pi.single i 1), ?_⟩
  rw [finiteNoDriftRootTuple_at, finiteNoDriftRootWord_single, Compressor.X, Word.eval_generator]

def finiteNoDriftRootExtend (α : Fin 4 → ZMod 5) : Fin 7 → ZMod 5 := Fin.append α (fun _ : Fin 3 => 0)

theorem finiteNoDriftRootExtend_injective : Function.Injective finiteNoDriftRootExtend := by
  intro α β he
  funext i
  have hh := congrFun he (i.castAdd 3)
  simpa only [finiteNoDriftRootExtend, Fin.append_left] using hh

theorem finiteNoDriftRootWord_extend (c : Fin 3) (α : Fin 4 → ZMod 5) :
    finiteNoDriftRootWord finiteNoDriftCoefficient c (finiteNoDriftRootExtend α) =
      finiteNoDriftRootWord finiteNoDriftPositiveCoefficient c α := by
  have hl : List.finRange 7 = (List.finRange 4).map (Fin.castAdd 3) ++
      (List.finRange 3).map (Fin.natAdd 4) := by decide +kernel
  unfold finiteNoDriftRootWord FinitePrimeFivePair.vectorWord
  rw [hl, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  simp only [Function.comp_apply, finiteNoDriftRootExtend, Fin.append_left, Fin.append_right,
    ZMod.val_zero, FinitePrimeFivePair.repeatWord, List.replicate_zero, List.flatten_nil,
    List.flatMap_nil, List.append_nil]
  simp [finiteNoDriftPositiveCoefficient]

end ThomGame.Analysis
