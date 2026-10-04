module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Infinite order of an alternating two-letter amalgam word

If both letters lie outside the amalgamating subgroup and come from
different factors, every positive power remains a nonempty reduced word.
The result uses mathlib's normal form theorem for the actual pushout.
-/

@[expose] public section
namespace ThomGame.AmalgamPowers

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
  (φ : ∀ i, H →* G i) (i j : ι) (hij : i ≠ j) (x : G i) (y : G j)
  (hx : x ∉ (φ i).range) (hy : y ∉ (φ j).range)

def alternatingWord (n : Nat) : Monoid.CoprodI.Word G where
  toList := (List.replicate n [⟨i, x⟩, ⟨j, y⟩]).flatten
  ne_one := by
    intro l hl
    obtain ⟨w, hw, hl⟩ := List.mem_flatten.mp hl
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · intro h
      change x = 1 at h
      apply hx
      rw [h]
      exact (φ i).range.one_mem
    · intro h
      change y = 1 at h
      apply hy
      rw [h]
      exact (φ j).range.one_mem
  chain_ne := by
    rw [List.isChain_flatten (by simp)]
    constructor
    · intro w hw
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hw
      simp [hij]
    · exact List.isChain_replicate_of_rel _ (by simp [hij.symm])

theorem alternatingWord_reduced (n : Nat) :
    Monoid.PushoutI.Reduced φ (alternatingWord φ i j hij x y hx hy n) := by
  intro l hl
  obtain ⟨w, hw, hl⟩ := List.mem_flatten.mp hl
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact hx
  · exact hy

theorem alternatingWord_prod (n : Nat) :
    Monoid.PushoutI.ofCoprodI (φ := φ) (alternatingWord φ i j hij x y hx hy n).prod =
      (Monoid.PushoutI.of (φ := φ) i x * Monoid.PushoutI.of (φ := φ) j y) ^ n := by
  induction n with
  | zero => simp [alternatingWord, Monoid.CoprodI.Word.prod]
  | succ n ih =>
    simp only [alternatingWord, Monoid.CoprodI.Word.prod] at ih ⊢
    simp only [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul,
      Monoid.PushoutI.ofCoprodI_of, ih, pow_succ']

include hij hx hy in
theorem alternating_pow_ne_one (hφ : ∀ k, Function.Injective (φ k)) (n : Nat) (hn : 0 < n) :
    (Monoid.PushoutI.of (φ := φ) i x * Monoid.PushoutI.of (φ := φ) j y) ^ n ≠ 1 := by
  intro hp
  have he : alternatingWord φ i j hij x y hx hy n = .empty :=
    Monoid.PushoutI.Reduced.eq_empty_of_mem_range hφ
      (alternatingWord_reduced φ i j hij x y hx hy n)
      ⟨1, by rw [map_one, alternatingWord_prod, hp]⟩
  have hl := congrArg Monoid.CoprodI.Word.toList he
  cases n with
  | zero => omega
  | succ n => simp [alternatingWord, List.replicate_succ] at hl

include hij hx hy in
theorem alternating_not_isOfFinOrder (hφ : ∀ k, Function.Injective (φ k)) :
    ¬ IsOfFinOrder (Monoid.PushoutI.of (φ := φ) i x * Monoid.PushoutI.of (φ := φ) j y) := by
  intro h
  obtain ⟨n, hn, hp⟩ := h.exists_pow_eq_one
  exact alternating_pow_ne_one φ i j hij x y hx hy hφ n hn hp

end ThomGame.AmalgamPowers
