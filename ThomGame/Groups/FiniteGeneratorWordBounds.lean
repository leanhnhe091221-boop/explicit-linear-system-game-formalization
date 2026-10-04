module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.Lattice.Fold

/-! Finite sets in a generated subgroup admit a common finite word-length bound. -/

@[expose] public noncomputable section
namespace ThomGame

variable {G : Type*} [Group G]

inductive GeneratorWordBound (S : Set G) : G → Nat → Prop
  | one : GeneratorWordBound S 1 0
  | generator (g : G) (hg : g ∈ S) : GeneratorWordBound S g 1
  | mul {g h : G} {n m : Nat} : GeneratorWordBound S g n → GeneratorWordBound S h m →
      GeneratorWordBound S (g * h) (n + m)
  | inv {g : G} {n : Nat} : GeneratorWordBound S g n → GeneratorWordBound S g⁻¹ n

theorem exists_generatorWordBound (S : Set G) (g : G) (hg : g ∈ Subgroup.closure S) :
    ∃ n : Nat, GeneratorWordBound S g n := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact ⟨1, .generator g hg⟩
  | one => exact ⟨0, .one⟩
  | mul g h hg hh ihg ihh =>
      obtain ⟨n, hn⟩ := ihg
      obtain ⟨m, hm⟩ := ihh
      exact ⟨n + m, hn.mul hm⟩
  | inv g hg ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, hn.inv⟩

theorem finiteSet_generatorWordBounds (S : Set G) (K : Finset G)
    (hK : ∀ g ∈ K, g ∈ Subgroup.closure S) :
    ∃ C : Nat, 0 < C ∧ ∀ g ∈ K, ∃ n ≤ C, GeneratorWordBound S g n := by
  classical
  let n : G → Nat := fun g => if hg : g ∈ K then Nat.find (exists_generatorWordBound S g (hK g hg)) else 0
  have hn (g : G) (hg : g ∈ K) : GeneratorWordBound S g (n g) := by
    dsimp only [n]
    rw [dite_eq_left hg]
    exact Nat.find_spec (exists_generatorWordBound S g (hK g hg))
  refine ⟨K.sup n + 1, Nat.zero_lt_succ _, ?_⟩
  intro g hg
  exact ⟨n g, (Finset.le_sup (f := n) hg).trans (Nat.le_succ _), hn g hg⟩

def finiteSetWordConstant (S : Set G) (K : Finset G) (hK : ∀ g ∈ K, g ∈ Subgroup.closure S) : Nat :=
  Classical.choose (finiteSet_generatorWordBounds S K hK)

theorem finiteSetWordConstant_pos (S : Set G) (K : Finset G) (hK : ∀ g ∈ K, g ∈ Subgroup.closure S) :
    0 < finiteSetWordConstant S K hK := (Classical.choose_spec (finiteSet_generatorWordBounds S K hK)).1

theorem finiteSetWordConstant_spec (S : Set G) (K : Finset G) (hK : ∀ g ∈ K, g ∈ Subgroup.closure S)
    (g : G) (hg : g ∈ K) : ∃ n ≤ finiteSetWordConstant S K hK, GeneratorWordBound S g n :=
  (Classical.choose_spec (finiteSet_generatorWordBounds S K hK)).2 g hg

end ThomGame
