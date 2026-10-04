module

public import ThomGame.Quantum.GameValue
public import Mathlib.Analysis.Convex.Hull

/-! Classical correlations are the convex hull of deterministic local responses.
Thus shared randomness is allowed, and the value is the actual supremum of the
game's payoff over this classical correlation set. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable {X Y A B : Type*}

noncomputable def deterministicCorrelation (alice : X → A) (bob : Y → B) :
    CorrelationTable X Y A B := by
  classical
  exact fun x y a b => if a = alice x ∧ b = bob y then 1 else 0

noncomputable def classicalCorrelations (X Y A B : Type*) :
    Set (CorrelationTable X Y A B) :=
  convexHull ℝ (Set.range (fun s : (X → A) × (Y → B) =>
    deterministicCorrelation s.1 s.2))

theorem deterministicCorrelation_mem_classical (alice : X → A) (bob : Y → B) :
    deterministicCorrelation alice bob ∈ classicalCorrelations X Y A B :=
  subset_convexHull ℝ _ ⟨(alice, bob), rfl⟩

theorem classicalCorrelations_nonempty [Nonempty A] [Nonempty B] :
    (classicalCorrelations X Y A B).Nonempty := by
  classical
  exact ⟨_, deterministicCorrelation_mem_classical (fun _ => Classical.arbitrary A)
    (fun _ => Classical.arbitrary B)⟩

variable [Fintype A] [Fintype B]

theorem deterministicCorrelation_isProbabilityTable (alice : X → A) (bob : Y → B) :
    IsProbabilityTable (deterministicCorrelation alice bob) := by
  classical
  constructor
  · intro x y a b
    unfold deterministicCorrelation
    split <;> norm_num
  · intro x y
    simp [deterministicCorrelation, ite_and]

theorem convex_probabilityTables :
    Convex ℝ {p : CorrelationTable X Y A B | IsProbabilityTable p} := by
  intro p hp q hq s t hs ht hst
  constructor
  · intro x y a b
    exact add_nonneg (mul_nonneg hs (hp.nonneg x y a b))
      (mul_nonneg ht (hq.nonneg x y a b))
  · intro x y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hp.normalized, hq.normalized, mul_one, hst]

theorem classicalCorrelation_isProbabilityTable {p : CorrelationTable X Y A B}
    (hp : p ∈ classicalCorrelations X Y A B) : IsProbabilityTable p := by
  apply convexHull_min _ convex_probabilityTables hp
  rintro _ ⟨⟨alice, bob⟩, rfl⟩
  exact deterministicCorrelation_isProbabilityTable alice bob

namespace FiniteGame

variable [Fintype X] [Fintype Y] (G : FiniteGame X Y A B)

noncomputable def omegaC : ℝ := G.value (classicalCorrelations X Y A B)

theorem success_deterministic (alice : X → A) (bob : Y → B) :
    G.success (deterministicCorrelation alice bob) =
      ∑ x, ∑ y, G.weight x y * G.payoff x y (alice x) (bob y) := by
  classical
  simp [success, answerScore, deterministicCorrelation, ite_and]

/-- Every uniform bound on deterministic payoffs also bounds shared-random payoffs. -/
theorem classical_success_le_of_deterministic {c : ℝ}
    (hc : ∀ alice bob, G.success (deterministicCorrelation alice bob) ≤ c)
    {p : CorrelationTable X Y A B} (hp : p ∈ classicalCorrelations X Y A B) :
    G.success p ≤ c := by
  apply convexHull_min (t := {p | G.success p ≤ c}) ?_ ?_ hp
  · rintro _ ⟨⟨alice, bob⟩, rfl⟩
    exact hc alice bob
  · intro p hp q hq s t hs ht hst
    change G.success (s • p + t • q) ≤ c
    rw [G.success_add, G.success_smul, G.success_smul]
    calc
      s * G.success p + t * G.success q ≤ s * c + t * c :=
        add_le_add (mul_le_mul_of_nonneg_left hp hs) (mul_le_mul_of_nonneg_left hq ht)
      _ = c := by rw [← add_mul, hst, one_mul]

theorem deterministic_success_le_omegaC (alice : X → A) (bob : Y → B) :
    G.success (deterministicCorrelation alice bob) ≤ G.omegaC :=
  G.success_le_value (fun _ hp => classicalCorrelation_isProbabilityTable hp)
    (deterministicCorrelation_mem_classical alice bob)

theorem omegaC_le_of_deterministic [Nonempty A] [Nonempty B] {c : ℝ}
    (hc : ∀ alice bob, G.success (deterministicCorrelation alice bob) ≤ c) :
    G.omegaC ≤ c := by
  apply csSup_le (classicalCorrelations_nonempty.image G.success)
  rintro _ ⟨p, hp, rfl⟩
  exact G.classical_success_le_of_deterministic hc hp

end FiniteGame
end ThomGame.Quantum
