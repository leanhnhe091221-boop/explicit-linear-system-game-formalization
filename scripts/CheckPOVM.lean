import ThomGame.Quantum.POVMGameValue
import ThomGame.Quantum.FinitePOVMCoordinates
import Lean.Util.CollectAxioms

set_option autoImplicit false

open ThomGame.Quantum

-- The input measurements are arbitrary positive effects summing to one.
#print POVM
#print FinitePOVMStrategy
#print CommutingPOVMStrategy

-- The embedding is fixed before all questions and preserves the entire table.
#check @POVM.exists_projective_dilation
#check @FinitePOVMStrategy.exists_projective
#check @FinitePOVMStrategy.exists_coordinates
#check @povmQuantumCorrelations_eq_quantumCorrelations
#check @FiniteGame.omegaQPOVM_eq_omegaQ
#check @FiniteGame.omegaQaPOVM_eq_omegaQa
#check @FiniteGame.omegaQcPOVM_eq_one_of_perfect

#print axioms POVM.exists_projective_dilation
#print axioms FinitePOVMStrategy.exists_projective
#print axioms FinitePOVMStrategy.exists_coordinates
#print axioms povmQuantumCorrelations_eq_quantumCorrelations
#print axioms FiniteGame.omegaQPOVM_eq_omegaQ
#print axioms FiniteGame.omegaQaPOVM_eq_omegaQa
#print axioms FiniteGame.omegaQcPOVM_eq_one_of_perfect

example {X Y A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (S : FinitePOVMStrategy X Y A B) :
    ∃ T : FiniteStrategy X Y A B, ∀ x y a b,
      T.correlation x y a b = S.correlation x y a b := by
  obtain ⟨T, hT⟩ := S.exists_projective
  exact ⟨T, fun x y a b => congrFun (congrFun (congrFun (congrFun hT x) y) a) b⟩

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[
    ``POVM.exists_projective_dilation,
    ``FinitePOVMStrategy.exists_projective,
    ``FinitePOVMStrategy.exists_coordinates,
    ``povmQuantumCorrelations_eq_quantumCorrelations,
    ``FiniteGame.omegaQPOVM_eq_omegaQ,
    ``FiniteGame.omegaQaPOVM_eq_omegaQa,
    ``FiniteGame.omegaQcPOVM_eq_one_of_perfect]
  for name in targets do
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
  logInfo "POVM semantic bridge axiom audit passed."
