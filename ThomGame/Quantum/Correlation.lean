module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.FunProp

/-! Finite real correlation tables, including positivity and normalization. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

abbrev CorrelationTable (X Y A B : Type*) := X → Y → A → B → ℝ

variable {X Y A B : Type*} [Fintype A] [Fintype B]

structure IsProbabilityTable (p : CorrelationTable X Y A B) : Prop where
  nonneg : ∀ x y a b, 0 ≤ p x y a b
  normalized : ∀ x y, ∑ a, ∑ b, p x y a b = 1

structure NoSignalling (p : CorrelationTable X Y A B) : Prop where
  alice : ∀ x y y' a, (∑ b, p x y a b) = ∑ b, p x y' a b
  bob : ∀ x x' y b, (∑ a, p x y a b) = ∑ a, p x' y a b

theorem IsProbabilityTable.le_one {p : CorrelationTable X Y A B}
    (hp : IsProbabilityTable p) (x : X) (y : Y) (a : A) (b : B) : p x y a b ≤ 1 := by
  have h₁ : p x y a b ≤ ∑ b, p x y a b :=
    Finset.single_le_sum (fun b _ => hp.nonneg x y a b) (Finset.mem_univ b)
  have h₂ : (∑ b, p x y a b) ≤ ∑ a, ∑ b, p x y a b :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hp.nonneg x y a b))
      (Finset.mem_univ a)
  exact (h₁.trans h₂).trans_eq (hp.normalized x y)

omit [Fintype A] [Fintype B] in
theorem continuous_table_entry (x : X) (y : Y) (a : A) (b : B) :
    Continuous (fun p : CorrelationTable X Y A B => p x y a b) := by fun_prop

theorem isClosed_probabilityTables :
    IsClosed {p : CorrelationTable X Y A B | IsProbabilityTable p} := by
  have he : {p : CorrelationTable X Y A B | IsProbabilityTable p} =
      {p | ∀ x y a b, 0 ≤ p x y a b} ∩ {p | ∀ x y, ∑ a, ∑ b, p x y a b = 1} := by
    ext p
    exact ⟨fun h => ⟨h.nonneg, h.normalized⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y => isClosed_iInter
      (fun a => isClosed_iInter (fun b => isClosed_le continuous_const
        (continuous_table_entry x y a b)))))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_eq (by fun_prop) continuous_const))

theorem isClosed_noSignalling :
    IsClosed {p : CorrelationTable X Y A B | NoSignalling p} := by
  have he : {p : CorrelationTable X Y A B | NoSignalling p} =
      {p | ∀ x y y' a, (∑ b, p x y a b) = ∑ b, p x y' a b} ∩
      {p | ∀ x x' y b, (∑ a, p x y a b) = ∑ a, p x' y a b} := by
    ext p
    exact ⟨fun h => ⟨h.alice, h.bob⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [he]
  apply IsClosed.inter <;> simp only [Set.ofPred_forall]
  · exact isClosed_iInter (fun x => isClosed_iInter (fun y => isClosed_iInter
      (fun y' => isClosed_iInter (fun a => isClosed_eq (by fun_prop) (by fun_prop)))))
  · exact isClosed_iInter (fun x => isClosed_iInter (fun x' => isClosed_iInter
      (fun y => isClosed_iInter (fun b => isClosed_eq (by fun_prop) (by fun_prop)))))

end ThomGame.Quantum
