module

public import ThomGame.Quantum.FinitePOVMDilation
public import ThomGame.Quantum.CommutingPOVMStrategy
public import ThomGame.Quantum.GameValue

/-! Correlation sets and game values for the manuscript's general POVM strategies.

Finite-dimensional dilation identifies the finite quantum correlation sets exactly,
and hence their closures. For commuting strategies the inclusion of projective
strategies suffices to transfer perfect strategies and values equal to one.
-/

@[expose] public section
namespace ThomGame.Quantum

variable (X Y A B : Type*) [Fintype A] [Fintype B]

def povmQuantumCorrelations : Set (CorrelationTable X Y A B) :=
  Set.range (FinitePOVMStrategy.correlation (X := X) (Y := Y) (A := A) (B := B))

def povmApproximateQuantumCorrelations : Set (CorrelationTable X Y A B) :=
  closure (povmQuantumCorrelations X Y A B)

/-- All complex Hilbert-space POVM strategies with cross-player commutation. -/
def povmCommutingCorrelations : Set (CorrelationTable X Y A B) :=
  {p | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (S : CommutingPOVMStrategy X Y A B H), S.correlation = p}

variable {X Y A B}

theorem povmQuantumCorrelations_eq_quantumCorrelations [Nonempty A] [Nonempty B] :
    povmQuantumCorrelations X Y A B = quantumCorrelations X Y A B := by
  apply Set.Subset.antisymm
  · rintro _ ⟨S, rfl⟩
    exact S.exists_projective
  · rintro _ ⟨S, rfl⟩
    exact ⟨S.toPOVM, S.toPOVM_correlation⟩

theorem povmApproximateQuantumCorrelations_eq_approximateQuantumCorrelations
    [Nonempty A] [Nonempty B] :
    povmApproximateQuantumCorrelations X Y A B =
      approximateQuantumCorrelations X Y A B := by
  unfold povmApproximateQuantumCorrelations approximateQuantumCorrelations
  rw [povmQuantumCorrelations_eq_quantumCorrelations]

theorem commuting_subset_povmCommuting :
    commutingCorrelations X Y A B ⊆ povmCommutingCorrelations X Y A B := by
  rintro _ ⟨H, hN, hI, hC, S, rfl⟩
  exact ⟨H, hN, hI, hC, S.toPOVM, S.toPOVM_correlation⟩

theorem povmQuantumCorrelation_isProbabilityTable [Nonempty A] [Nonempty B]
    {p : CorrelationTable X Y A B} (hp : p ∈ povmQuantumCorrelations X Y A B) :
    IsProbabilityTable p := by
  rw [povmQuantumCorrelations_eq_quantumCorrelations] at hp
  exact quantumCorrelation_isProbabilityTable hp

theorem povmApproximateQuantumCorrelation_isProbabilityTable [Nonempty A] [Nonempty B]
    {p : CorrelationTable X Y A B}
    (hp : p ∈ povmApproximateQuantumCorrelations X Y A B) : IsProbabilityTable p := by
  rw [povmApproximateQuantumCorrelations_eq_approximateQuantumCorrelations] at hp
  exact approximateQuantumCorrelation_isProbabilityTable hp

theorem povmCommutingCorrelation_isProbabilityTable {p : CorrelationTable X Y A B}
    (hp : p ∈ povmCommutingCorrelations X Y A B) : IsProbabilityTable p := by
  obtain ⟨H, hN, hI, hC, S, rfl⟩ := hp
  exact S.isProbabilityTable

theorem povmCommutingCorrelations_nonempty [Nonempty A] [Nonempty B] :
    (povmCommutingCorrelations X Y A B).Nonempty :=
  commutingCorrelations_nonempty.mono commuting_subset_povmCommuting

namespace FiniteGame

variable [Fintype X] [Fintype Y] (G : FiniteGame X Y A B)

noncomputable def omegaQPOVM : ℝ := G.value (povmQuantumCorrelations X Y A B)
noncomputable def omegaQaPOVM : ℝ := G.value (povmApproximateQuantumCorrelations X Y A B)
noncomputable def omegaQcPOVM : ℝ := G.value (povmCommutingCorrelations X Y A B)

theorem commutingPOVMStrategy_success_le {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : CommutingPOVMStrategy X Y A B H) :
    G.success S.correlation ≤ G.omegaQcPOVM :=
  G.success_le_value (fun _ hp => povmCommutingCorrelation_isProbabilityTable hp)
    ⟨H, inferInstance, inferInstance, inferInstance, S, rfl⟩

/-- A perfect projective commuting strategy remains perfect among general POVMs. -/
theorem omegaQcPOVM_eq_one_of_perfect {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : CommutingStrategy X Y A B H)
    (hS : G.success S.correlation = 1) : G.omegaQcPOVM = 1 := by
  have hp : S.toPOVM.correlation ∈ povmCommutingCorrelations X Y A B :=
    ⟨H, inferInstance, inferInstance, inferInstance, S.toPOVM, rfl⟩
  apply le_antisymm
  · exact G.value_le_one ⟨S.toPOVM.correlation, hp⟩
      (fun _ h => povmCommutingCorrelation_isProbabilityTable h)
  · simpa only [S.toPOVM_correlation, hS] using G.commutingPOVMStrategy_success_le S.toPOVM

variable [Nonempty A] [Nonempty B]

theorem omegaQPOVM_eq_omegaQ : G.omegaQPOVM = G.omegaQ := by
  unfold omegaQPOVM omegaQ
  rw [povmQuantumCorrelations_eq_quantumCorrelations]

theorem omegaQaPOVM_eq_omegaQa : G.omegaQaPOVM = G.omegaQa := by
  unfold omegaQaPOVM omegaQa
  rw [povmApproximateQuantumCorrelations_eq_approximateQuantumCorrelations]

theorem omegaQPOVM_eq_omegaQaPOVM : G.omegaQPOVM = G.omegaQaPOVM := by
  rw [G.omegaQPOVM_eq_omegaQ, G.omegaQaPOVM_eq_omegaQa]
  exact G.omegaQ_eq_omegaQa

theorem omegaQcPOVM_le_one : G.omegaQcPOVM ≤ 1 :=
  G.value_le_one povmCommutingCorrelations_nonempty
    (fun _ hp => povmCommutingCorrelation_isProbabilityTable hp)

theorem omegaQc_le_omegaQcPOVM : G.omegaQc ≤ G.omegaQcPOVM :=
  csSup_le_csSup
    (G.success_bddAbove (fun _ hp => povmCommutingCorrelation_isProbabilityTable hp))
    (commutingCorrelations_nonempty.image G.success)
    (Set.image_mono commuting_subset_povmCommuting)

/-- Projective commuting value one transfers using only inclusion and the
probability bound; no commuting POVM dilation is needed. -/
theorem omegaQcPOVM_eq_one_of_omegaQc_eq_one (h : G.omegaQc = 1) :
    G.omegaQcPOVM = 1 := by
  apply le_antisymm G.omegaQcPOVM_le_one
  simpa only [h] using G.omegaQc_le_omegaQcPOVM

end FiniteGame
end ThomGame.Quantum
