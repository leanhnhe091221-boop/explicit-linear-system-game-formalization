module

public import ThomGame.Quantum.FiniteGame
public import ThomGame.Quantum.CorrelationSets
public import Mathlib.Topology.Order.Monotone

/-! Actual game values, and invariance of the quantum value under correlation closure. -/

@[expose] public section
namespace ThomGame.Quantum.FiniteGame

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  (G : FiniteGame X Y A B)

noncomputable def value (K : Set (CorrelationTable X Y A B)) : ℝ := sSup (G.success '' K)

noncomputable def omegaQ : ℝ := G.value (quantumCorrelations X Y A B)
noncomputable def omegaQa : ℝ := G.value (approximateQuantumCorrelations X Y A B)
noncomputable def omegaQc : ℝ := G.value (commutingCorrelations X Y A B)

theorem success_bddAbove {K : Set (CorrelationTable X Y A B)}
    (hK : ∀ p ∈ K, IsProbabilityTable p) : BddAbove (G.success '' K) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact G.success_le_one (hK p hp)

theorem success_le_value {K : Set (CorrelationTable X Y A B)}
    (hK : ∀ p ∈ K, IsProbabilityTable p) {p : CorrelationTable X Y A B} (hp : p ∈ K) :
    G.success p ≤ G.value K := le_csSup (G.success_bddAbove hK) ⟨p, hp, rfl⟩

theorem value_le_one {K : Set (CorrelationTable X Y A B)} (hne : K.Nonempty)
    (hK : ∀ p ∈ K, IsProbabilityTable p) : G.value K ≤ 1 := by
  apply csSup_le (hne.image G.success)
  rintro _ ⟨p, hp, rfl⟩
  exact G.success_le_one (hK p hp)

theorem value_nonneg {K : Set (CorrelationTable X Y A B)} (hne : K.Nonempty)
    (hK : ∀ p ∈ K, IsProbabilityTable p) : 0 ≤ G.value K := by
  obtain ⟨p, hp⟩ := hne
  exact (G.success_nonneg (hK p hp)).trans (G.success_le_value hK hp)

/-- A continuous payoff has the same supremum on a nonempty set and its closure. -/
theorem value_closure {K : Set (CorrelationTable X Y A B)} (hne : K.Nonempty)
    (hK : ∀ p ∈ K, IsProbabilityTable p) : G.value (closure K) = G.value K := by
  have hc : ∀ p ∈ closure K, IsProbabilityTable p :=
    fun _ hp => closure_minimal hK isClosed_probabilityTables hp
  apply le_antisymm
  · apply csSup_le ((hne.mono subset_closure).image G.success)
    rintro _ ⟨p, hp, rfl⟩
    have hs : IsClosed {p | G.success p ≤ G.value K} :=
      isClosed_le G.continuous_success continuous_const
    exact closure_minimal (fun p hp => G.success_le_value hK hp) hs hp
  · exact csSup_le_csSup (G.success_bddAbove hc) (hne.image G.success)
      (Set.image_mono subset_closure)

variable [Nonempty A] [Nonempty B]

theorem omegaQ_eq_omegaQa : G.omegaQ = G.omegaQa :=
  (G.value_closure quantumCorrelations_nonempty
    (fun _ hp => quantumCorrelation_isProbabilityTable hp)).symm

theorem omegaQ_le_one : G.omegaQ ≤ 1 :=
  G.value_le_one quantumCorrelations_nonempty (fun _ hp => quantumCorrelation_isProbabilityTable hp)

theorem omegaQa_le_one : G.omegaQa ≤ 1 :=
  G.value_le_one approximateQuantumCorrelations_nonempty
    (fun _ hp => approximateQuantumCorrelation_isProbabilityTable hp)

theorem omegaQc_le_one : G.omegaQc ≤ 1 :=
  G.value_le_one commutingCorrelations_nonempty
    (fun _ hp => commutingCorrelation_isProbabilityTable hp)

theorem omegaQ_nonneg : 0 ≤ G.omegaQ :=
  G.value_nonneg quantumCorrelations_nonempty (fun _ hp => quantumCorrelation_isProbabilityTable hp)

theorem omegaQa_nonneg : 0 ≤ G.omegaQa := by rw [← G.omegaQ_eq_omegaQa]; exact G.omegaQ_nonneg

theorem omegaQc_nonneg : 0 ≤ G.omegaQc :=
  G.value_nonneg commutingCorrelations_nonempty
    (fun _ hp => commutingCorrelation_isProbabilityTable hp)

theorem omegaQ_le_omegaQc : G.omegaQ ≤ G.omegaQc :=
  csSup_le_csSup (G.success_bddAbove (fun _ hp => commutingCorrelation_isProbabilityTable hp))
    (quantumCorrelations_nonempty.image G.success) (Set.image_mono quantum_subset_commuting)

omit [Nonempty A] [Nonempty B] in
theorem finiteStrategy_success_le (S : FiniteStrategy X Y A B) : G.success S.correlation ≤ G.omegaQ :=
  G.success_le_value (fun _ hp => quantumCorrelation_isProbabilityTable hp) ⟨S, rfl⟩

omit [Nonempty A] [Nonempty B] in
theorem commutingStrategy_success_le {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : CommutingStrategy X Y A B H) :
    G.success S.correlation ≤ G.omegaQc :=
  G.success_le_value (fun _ hp => commutingCorrelation_isProbabilityTable hp)
    ⟨H, inferInstance, inferInstance, inferInstance, S, rfl⟩

end ThomGame.Quantum.FiniteGame
