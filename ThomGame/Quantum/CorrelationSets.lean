module

public import ThomGame.Quantum.FiniteStrategy

/-! Quantum, approximately quantum, and commuting correlation sets. -/

@[expose] public section
namespace ThomGame.Quantum

variable (X Y A B : Type*) [Fintype A] [Fintype B]

def quantumCorrelations : Set (CorrelationTable X Y A B) :=
  Set.range (FiniteStrategy.correlation (X := X) (Y := Y) (A := A) (B := B))

def approximateQuantumCorrelations : Set (CorrelationTable X Y A B) :=
  closure (quantumCorrelations X Y A B)

/-- All complex Hilbert-space projective strategies with cross-player commutation. -/
def commutingCorrelations : Set (CorrelationTable X Y A B) :=
  {p | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (S : CommutingStrategy X Y A B H), S.correlation = p}

variable {X Y A B}

theorem quantumCorrelation_isProbabilityTable {p : CorrelationTable X Y A B}
    (hp : p ∈ quantumCorrelations X Y A B) : IsProbabilityTable p := by
  obtain ⟨S, rfl⟩ := hp
  exact S.isProbabilityTable

theorem quantumCorrelation_noSignalling {p : CorrelationTable X Y A B}
    (hp : p ∈ quantumCorrelations X Y A B) : NoSignalling p := by
  obtain ⟨S, rfl⟩ := hp
  exact S.noSignalling

theorem approximateQuantumCorrelation_isProbabilityTable {p : CorrelationTable X Y A B}
    (hp : p ∈ approximateQuantumCorrelations X Y A B) : IsProbabilityTable p :=
  closure_minimal (fun _ hp => quantumCorrelation_isProbabilityTable hp)
    isClosed_probabilityTables hp

theorem approximateQuantumCorrelation_noSignalling {p : CorrelationTable X Y A B}
    (hp : p ∈ approximateQuantumCorrelations X Y A B) : NoSignalling p :=
  closure_minimal (fun _ hp => quantumCorrelation_noSignalling hp) isClosed_noSignalling hp

theorem commutingCorrelation_isProbabilityTable {p : CorrelationTable X Y A B}
    (hp : p ∈ commutingCorrelations X Y A B) : IsProbabilityTable p := by
  obtain ⟨H, hN, hI, hC, S, rfl⟩ := hp
  exact S.isProbabilityTable

theorem commutingCorrelation_noSignalling {p : CorrelationTable X Y A B}
    (hp : p ∈ commutingCorrelations X Y A B) : NoSignalling p := by
  obtain ⟨H, hN, hI, hC, S, rfl⟩ := hp
  exact S.noSignalling

theorem quantum_subset_approximateQuantum :
    quantumCorrelations X Y A B ⊆ approximateQuantumCorrelations X Y A B := subset_closure

theorem quantum_subset_commuting : quantumCorrelations X Y A B ⊆ commutingCorrelations X Y A B := by
  rintro _ ⟨S, rfl⟩
  exact ⟨BipartiteSpace S.dimAlice S.dimBob, inferInstance, inferInstance, inferInstance,
    S.toCommuting, rfl⟩

theorem quantumCorrelations_nonempty [Nonempty A] [Nonempty B] :
    (quantumCorrelations X Y A B).Nonempty := by
  classical
  let S : FiniteStrategy X Y A B := FiniteStrategy.deterministic
    (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary B)
  exact ⟨S.correlation, ⟨S, rfl⟩⟩

theorem approximateQuantumCorrelations_nonempty [Nonempty A] [Nonempty B] :
    (approximateQuantumCorrelations X Y A B).Nonempty :=
  quantumCorrelations_nonempty.mono quantum_subset_approximateQuantum

theorem commutingCorrelations_nonempty [Nonempty A] [Nonempty B] :
    (commutingCorrelations X Y A B).Nonempty :=
  quantumCorrelations_nonempty.mono quantum_subset_commuting

end ThomGame.Quantum
