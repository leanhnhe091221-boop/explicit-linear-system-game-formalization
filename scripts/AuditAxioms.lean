import ThomGame
import Lean.Util.CollectAxioms

/-! Reject any project theorem with an axiom outside Lean's usual foundations.
This complements, rather than replaces, review of theorem types and definitions.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (name.toString.startsWith "ThomGame." || name.toString.startsWith "_private.ThomGame.") && info.isTheorem then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} ThomGame theorems. Allowed: propext, Classical.choice, Quot.sound."

#print axioms ThomGame.Lambda.Certificate.normalized_eq_table
#print axioms ThomGame.Lambda.normalizationEquiv_of
#print axioms ThomGame.Construction.no_solution
#print axioms ThomGame.Construction.no_perfect_deterministic
#print axioms ThomGame.Construction.row_count
#print axioms ThomGame.Construction.col_count
#print axioms ThomGame.Construction.nonzero_count
#print axioms ThomGame.Construction.rhs_nonzero_row_number
#print axioms ThomGame.Construction.rowEquiv_number
#print axioms ThomGame.Construction.colEquiv_number
#print axioms ThomGame.Construction.A_eq_one_iff
#print axioms ThomGame.Construction.A_nonzero_count
#print axioms ThomGame.Construction.b_formula
#print axioms ThomGame.Construction.A_b_no_solution
#print axioms ThomGame.Construction.J_sigma_central
#print axioms ThomGame.Construction.wheelSolutionEquiv_J
#print axioms ThomGame.SolutionGroup.Model.toHom_unique
#print axioms ThomGame.Lambda.canonical_cyclicallyReduced
#print axioms ThomGame.Construction.wheelWord_cyclicallyReduced
#print axioms ThomGame.Construction.involutionPresentation_collegial
#print axioms ThomGame.Construction.lambdaToInvolution_J
#print axioms ThomGame.Wheel.Family.solution_word_product
#print axioms ThomGame.Construction.involutionToSigma_J
#print axioms ThomGame.Construction.lambdaToSigma_J
#print axioms ThomGame.InvolutionPresentation.Model.toHom_unique
#print axioms ThomGame.Lambda.JElement_central
#print axioms ThomGame.Lambda.stable_conjugates_obstruction
#print axioms ThomGame.Lambda.hom_J_eq_one_of_obstruction_eq_one
#print axioms ThomGame.CosetReversal.reverse_mul
#print axioms ThomGame.InvolutionPermutation.regular_injective
#print axioms ThomGame.InvolutionPermutation.Reversal.pair_square
#print axioms ThomGame.Construction.involutionToPermutation_comp_lambda
#print axioms ThomGame.Construction.lambdaToInvolution_injective
#print axioms ThomGame.Construction.J_star_eq_one_iff
#print axioms ThomGame.Compressor.t_conjugate_subgroup_le
#print axioms ThomGame.Compressor.compression_generates
#print axioms ThomGame.Compressor.elementarySubgroup_normal
#print axioms ThomGame.Double.copyHom_injective
#print axioms ThomGame.Double.amalgamEquiv
#print axioms ThomGame.Double.amalgamEquiv_copy
#print axioms ThomGame.Double.obstruction_not_isOfFinOrder
#print axioms ThomGame.Double.difference_commutes
#print axioms ThomGame.Double.hom_obstruction_eq_one_of_normalizes_centralizer
#print axioms ThomGame.CentralTwist.base_j_ne_one
#print axioms ThomGame.CentralTwist.twist
#print axioms ThomGame.Lambda.Model.toHom_double
#print axioms ThomGame.Lambda.hnnEquiv_double
#print axioms ThomGame.Lambda.hnnEquiv
#print axioms ThomGame.Lambda.hnnEquiv_J
#print axioms ThomGame.Lambda.JElement_ne_one_of_strict_compression
#print axioms ThomGame.Lambda.doubleToLambda_injective_of_strict_compression
#print axioms ThomGame.Lambda.hom_J_eq_one_of_normalizes_centralizer
#print axioms ThomGame.LaurentModel.representation
#print axioms ThomGame.LaurentModel.eval_rawRelator
#print axioms ThomGame.LaurentModel.representation_positive_entry
#print axioms ThomGame.LaurentModel.representation_backward_entry
#print axioms ThomGame.Compressor.backwardConjugate_not_mem_positiveSubgroup
#print axioms ThomGame.Compressor.t_conjugate_subgroup_lt
#print axioms ThomGame.Double.obstruction_infiniteOrder
#print axioms ThomGame.Double.toLambda_injective
#print axioms ThomGame.Lambda.doubleHNNEquiv
#print axioms ThomGame.Lambda.JElement_ne_one
#print axioms ThomGame.Construction.J_star_ne_one
#print axioms ThomGame.CentralQuotient.Datum.projection_eq_one_iff
#print axioms ThomGame.CentralQuotient.Datum.injective_of_quotient_injective
#print axioms ThomGame.InvolutionPresentation.homogeneousEquiv
#print axioms ThomGame.InvolutionPresentation.forgetParity_eq_one_iff
#print axioms ThomGame.InvolutionPresentation.forgetParity_not_surjective
#print axioms ThomGame.SolutionGroup.involutionEquiv
#print axioms ThomGame.SolutionGroup.homogeneous_involutionPresentation
#print axioms ThomGame.SolutionGroup.homogeneousEquiv
#print axioms ThomGame.SolutionGroup.forgetParity_eq_one_iff
#print axioms ThomGame.SolutionGroup.forgetParity_not_surjective
#print axioms ThomGame.SolutionGroup.triple_commutes
#print axioms ThomGame.SolutionGroup.Model.row_word_product
#print axioms ThomGame.SolutionGroup.triangularEquiv
#print axioms ThomGame.Construction.homogeneousInvolutionToSigma_x
#print axioms ThomGame.Construction.homogeneous_square
#print axioms ThomGame.Construction.involutionToSigma_kernel_of_homogeneous_injective
#print axioms ThomGame.Construction.involutionToSigma_injective_of_homogeneous_injective
#print axioms ThomGame.InvolutionDerivation.presentedEquiv
#print axioms ThomGame.InvolutionDerivation.word_eq_iff_derives
#print axioms ThomGame.InvolutionDerivation.word_eq_iff_steps
#print axioms ThomGame.InvolutionDerivation.word_eq_iff_trace
#print axioms ThomGame.InvolutionDerivation.valid_sign
#print axioms ThomGame.InvolutionDerivation.sign_eq_character
#print axioms ThomGame.InvolutionDerivation.check_eq_true
#print axioms ThomGame.SolutionGroup.word_eq_iff_character_trace
#print axioms ThomGame.SolutionGroup.J_eq_one_iff_closed_odd_trace
#print axioms ThomGame.SolutionGroup.word_eq_iff_checked_trace
#print axioms ThomGame.Construction.sigmaTrace_sign
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_checked_odd_trace
#print axioms ThomGame.Pictures.Diagram.steps
#print axioms ThomGame.Pictures.Diagram.boundary_eq
#print axioms ThomGame.Pictures.diagram_of_valid
#print axioms ThomGame.Pictures.word_eq_iff_diagram
#print axioms ThomGame.Pictures.Diagram.adjoint_adjoint
#print axioms ThomGame.Pictures.Diagram.boundary_close
#print axioms ThomGame.Pictures.Frame.replace_sign
#print axioms ThomGame.Pictures.Frame.replace_size_lt
#print axioms ThomGame.Pictures.Diagram.exists_minimal
#print axioms ThomGame.Pictures.Diagram.minimal_filling
#print axioms ThomGame.SolutionGroup.word_eq_iff_minimal_diagram
#print axioms ThomGame.Construction.sigmaDiagram_sign
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_odd_diagram
#print axioms ThomGame.Construction.involution_no_closed_odd_diagram
#print axioms ThomGame.Pictures.Pairing.edge_eq_iff
#print axioms ThomGame.Pictures.Pairing.edge_fiber_nat_card
#print axioms ThomGame.Pictures.Pairing.dart_card_eq_twice_edge_card
#print axioms ThomGame.Pictures.Port.incidentEquiv
#print axioms ThomGame.Pictures.PortGraph.degree_hub
#print axioms ThomGame.Pictures.PortGraph.degree_joint
#print axioms ThomGame.Pictures.PortGraph.twin_compPorts
#print axioms ThomGame.Pictures.PortGraph.twin_tensorPorts
#print axioms ThomGame.Pictures.Diagram.hubLabel_index
#print axioms ThomGame.Pictures.Diagram.graph_hub_card
#print axioms ThomGame.Pictures.Diagram.graph_sign
#print axioms ThomGame.Pictures.Diagram.graph_boundary_eq
#print axioms ThomGame.Pictures.PortGraph.degree_sum
#print axioms ThomGame.Pictures.PortGraph.not_adj_self_hub
#print axioms ThomGame.Pictures.PortGraph.rotation_sameCycle_iff
#print axioms ThomGame.Pictures.PortGraph.circuit_eq_iff
#print axioms ThomGame.SolutionGroup.rowGraph_port_label
#print axioms ThomGame.SolutionGroup.rowGraph_not_adj_self_hub
#print axioms ThomGame.SolutionGroup.word_eq_iff_extracted_graph
#print axioms ThomGame.Construction.sigmaDiagram_graph_sign
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_odd_extracted_graph
#print axioms ThomGame.Pictures.Pairing.smooth_joins_partners
#print axioms ThomGame.Pictures.Pairing.ext_edge_relation
#print axioms ThomGame.Pictures.PortGraph.smooth_joint_card
#print axioms ThomGame.Pictures.PortGraph.smooth_edge_card
#print axioms ThomGame.Pictures.PortGraph.smooth_sign
#print axioms ThomGame.Pictures.PortGraph.smooth_rotation
#print axioms ThomGame.Pictures.PortGraph.loop_wire_component
#print axioms ThomGame.Pictures.PortGraph.smooth_wireConnected_iff
#print axioms ThomGame.Pictures.Smoothing.exists_without_junctions
#print axioms ThomGame.Pictures.Smoothing.hubLabel
#print axioms ThomGame.Pictures.Smoothing.hubFlip
#print axioms ThomGame.Pictures.Smoothing.sign
#print axioms ThomGame.Pictures.Smoothing.joint_card
#print axioms ThomGame.Pictures.Smoothing.edge_card
#print axioms ThomGame.Pictures.Smoothing.terminal_surjective
#print axioms ThomGame.Pictures.Smoothing.wire_iff_final_edge
#print axioms ThomGame.Pictures.Smoothing.terminalPairing_edge_iff
#print axioms ThomGame.Pictures.Smoothing.terminalPairing_independent
#print axioms ThomGame.Pictures.Smoothing.unique_other_terminal
#print axioms ThomGame.Pictures.Diagram.exists_smoothed_graph
#print axioms ThomGame.SolutionGroup.word_eq_iff_smoothed_graph
#print axioms ThomGame.Construction.smoothed_sigma_sign
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_smoothed_graph
#print axioms ThomGame.Pictures.FiniteReturn.Advances.sameCycle_iff
#print axioms ThomGame.Pictures.FiniteReturn.Advances.orbitMap_injective
#print axioms ThomGame.Pictures.PortGraph.smooth_circuit_advances
#print axioms ThomGame.Pictures.PortGraph.smooth_sameCycle_iff
#print axioms ThomGame.Pictures.PortGraph.smoothCircuitMap_injective
#print axioms ThomGame.Pictures.PortGraph.smoothCircuitMap_surjective_of_not_loop
#print axioms ThomGame.Pictures.PortGraph.loop_circuits_ne
#print axioms ThomGame.Pictures.PortGraph.smoothCircuitMap_range_of_loop
#print axioms ThomGame.Pictures.PortGraph.smooth_circuit_card
#print axioms ThomGame.Pictures.PortGraph.smooth_ribbonEuler
#print axioms ThomGame.Pictures.Smoothing.sameCircuit_iff
#print axioms ThomGame.Pictures.Smoothing.circuit_card
#print axioms ThomGame.Pictures.Smoothing.ribbonEuler
#print axioms ThomGame.Pictures.Smoothing.portRotation
#print axioms ThomGame.Pictures.Smoothing.terminalCircuitStep_independent
#print axioms ThomGame.Pictures.Smoothing.circuitEmbedding_range_iff
#print axioms ThomGame.Pictures.Smoothing.discarded_circuit_card
#print axioms ThomGame.Pictures.Smoothing.circles_length_independent
#print axioms ThomGame.Construction.smoothed_sigma_circuit_card
#print axioms ThomGame.Construction.smoothed_sigma_ribbonEuler
#print axioms ThomGame.Construction.smoothed_sigma_circuit_range

#check ThomGame.Construction.no_solution
#check ThomGame.Construction.no_perfect_deterministic
#check ThomGame.Construction.row_count
#check ThomGame.Construction.col_count
#check ThomGame.Construction.nonzero_count
#check ThomGame.Construction.A
#check ThomGame.Construction.b
#check ThomGame.Construction.A_b_no_solution
#check ThomGame.Construction.SigmaGroup
#check ThomGame.Construction.J_sigma_square
#check ThomGame.Construction.J_sigma_central
#check ThomGame.Construction.involutionPresentation_collegial
#check ThomGame.Construction.lambdaToSigma
#check ThomGame.Construction.lambdaToSigma_of
#check ThomGame.Construction.lambdaToSigma_J
#check ThomGame.Lambda.JElement_square
#check ThomGame.Lambda.JElement_central
#check ThomGame.Lambda.stable_conjugates_obstruction
#check ThomGame.Construction.lambdaToInvolution_injective
#check ThomGame.Construction.involutionToPermutation_comp_lambda
#check ThomGame.Construction.J_star_eq_one_iff
#check ThomGame.Compressor.positiveSubgroup
#check ThomGame.Compressor.t_conjugate_subgroup_le
#check ThomGame.Compressor.compression_generates
#check ThomGame.Compressor.elementarySubgroup_normal
#check ThomGame.Double.amalgamEquiv
#check ThomGame.Double.copyHom_injective
#check ThomGame.Double.obstruction_not_isOfFinOrder
#check ThomGame.Double.difference_commutes
#check ThomGame.Double.hom_obstruction_eq_one_of_normalizes_centralizer
#check ThomGame.Lambda.hnnEquiv
#check ThomGame.Lambda.JElement_ne_one_of_strict_compression
#check ThomGame.Lambda.doubleToLambda_injective_of_strict_compression
#check ThomGame.Lambda.hom_J_eq_one_of_normalizes_centralizer
#check ThomGame.LaurentModel.representation
#check ThomGame.LaurentModel.eval_rawRelator
#check ThomGame.LaurentModel.representation_positive_entry
#check ThomGame.Compressor.backwardConjugate_not_mem_positiveSubgroup
#check ThomGame.Compressor.h_not_mem_conjugate_positiveSubgroup
#check ThomGame.Compressor.t_conjugate_subgroup_lt
#check ThomGame.Double.obstruction_infiniteOrder
#check ThomGame.Double.toLambda_injective
#check ThomGame.Lambda.doubleHNNEquiv
#check ThomGame.Lambda.JElement_ne_one
#check ThomGame.Construction.J_star_ne_one
#check ThomGame.CentralQuotient.Datum.subgroup
#check ThomGame.CentralQuotient.Datum.projection_eq_one_iff
#check ThomGame.CentralQuotient.Datum.injective_of_quotient_injective
#check ThomGame.InvolutionPresentation.homogeneousEquiv
#check ThomGame.InvolutionPresentation.forgetParity_eq_one_iff
#check ThomGame.InvolutionPresentation.forgetParity_not_surjective
#check ThomGame.SolutionGroup.involutionEquiv
#check ThomGame.SolutionGroup.homogeneous_involutionPresentation
#check ThomGame.SolutionGroup.homogeneousEquiv
#check ThomGame.SolutionGroup.forgetParity_eq_one_iff
#check ThomGame.SolutionGroup.forgetParity_not_surjective
#check ThomGame.SolutionGroup.triple_commutes
#check ThomGame.SolutionGroup.Model.row_word_product
#check ThomGame.SolutionGroup.triangularEquiv
#check ThomGame.SolutionGroup.triangularEquiv_J
#check ThomGame.Construction.homogeneousInvolutionToSigma
#check ThomGame.Construction.homogeneousInvolutionToSigma_x
#check ThomGame.Construction.homogeneous_square
#check ThomGame.Construction.involutionToSigma_kernel_of_homogeneous_injective
#check ThomGame.Construction.involutionToSigma_injective_of_homogeneous_injective
#check ThomGame.InvolutionDerivation.Basic
#check ThomGame.InvolutionDerivation.Step
#check ThomGame.InvolutionDerivation.Move
#check ThomGame.InvolutionDerivation.Valid
#check ThomGame.InvolutionDerivation.presentedEquiv
#check ThomGame.InvolutionDerivation.word_eq_iff_derives
#check ThomGame.InvolutionDerivation.word_eq_iff_steps
#check ThomGame.InvolutionDerivation.word_eq_iff_trace
#check ThomGame.InvolutionDerivation.valid_sign
#check ThomGame.InvolutionDerivation.sign_eq_character
#check ThomGame.InvolutionDerivation.check_eq_true
#check ThomGame.SolutionGroup.word_eq_iff_character_trace
#check ThomGame.SolutionGroup.J_eq_one_iff_closed_odd_trace
#check ThomGame.SolutionGroup.word_eq_iff_checked_trace
#check ThomGame.Construction.sigmaTrace_sign
#check ThomGame.Construction.J_sigma_eq_one_iff_checked_odd_trace
#check ThomGame.Construction.sigmaTrace_odd_row_number
#print ThomGame.Pictures.Diagram
#print ThomGame.Pictures.Frame
#check ThomGame.Pictures.Diagram.steps
#check ThomGame.Pictures.Diagram.boundary_eq
#check ThomGame.Pictures.diagram_of_valid
#check ThomGame.Pictures.word_eq_iff_diagram
#check ThomGame.Pictures.Diagram.adjoint_adjoint
#check ThomGame.Pictures.Diagram.boundary_close
#check ThomGame.Pictures.Frame.replace_sign
#check ThomGame.Pictures.Frame.replace_size_lt
#check ThomGame.Pictures.Diagram.exists_minimal
#check ThomGame.Pictures.Diagram.minimal_filling
#check ThomGame.SolutionGroup.word_eq_iff_minimal_diagram
#check ThomGame.Construction.sigmaDiagram_sign
#check ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_odd_diagram
#check ThomGame.Construction.involution_no_closed_odd_diagram
#print ThomGame.Pictures.Pairing
#print ThomGame.Pictures.Port
#print ThomGame.Pictures.PortGraph
#check ThomGame.Pictures.Pairing.edge_eq_iff
#check ThomGame.Pictures.Pairing.edge_fiber_nat_card
#check ThomGame.Pictures.Pairing.dart_card_eq_twice_edge_card
#check ThomGame.Pictures.Port.incidentEquiv
#check ThomGame.Pictures.PortGraph.degree_top
#check ThomGame.Pictures.PortGraph.degree_bottom
#check ThomGame.Pictures.PortGraph.degree_hub
#check ThomGame.Pictures.PortGraph.degree_joint
#check ThomGame.Pictures.PortGraph.twin_compPorts
#check ThomGame.Pictures.PortGraph.twin_tensorPorts
#check ThomGame.Pictures.Diagram.graph
#check ThomGame.Pictures.Diagram.hubIndex
#check ThomGame.Pictures.Diagram.hubLabel_index
#check ThomGame.Pictures.Diagram.graph_hub_card
#check ThomGame.Pictures.Diagram.graph_sign
#check ThomGame.Pictures.Diagram.graph_boundary_eq
#check ThomGame.Pictures.PortGraph.degree_sum
#check ThomGame.Pictures.PortGraph.not_adj_self_hub
#check ThomGame.Pictures.PortGraph.rotation_sameCycle_iff
#check ThomGame.Pictures.PortGraph.circuit_eq_iff
#check ThomGame.SolutionGroup.rowGraph_port_label
#check ThomGame.SolutionGroup.rowGraph_not_adj_self_hub
#check ThomGame.SolutionGroup.word_eq_iff_extracted_graph
#check ThomGame.Construction.sigmaDiagram_graph_sign
#check ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_odd_extracted_graph
#print ThomGame.Pictures.Pairing.splice
#print ThomGame.Pictures.PortGraph.smoothCircles
#print ThomGame.Pictures.PortGraph.WireStep
#print ThomGame.Pictures.PortGraph.WireConnected
#print ThomGame.Pictures.Smoothing
#check ThomGame.Pictures.Pairing.smooth_joins_partners
#check ThomGame.Pictures.PortGraph.smooth_joint_card
#check ThomGame.Pictures.PortGraph.smooth_edge_card
#check ThomGame.Pictures.PortGraph.smooth_sign
#check ThomGame.Pictures.PortGraph.smooth_rotation
#check ThomGame.Pictures.PortGraph.loop_wire_component
#check ThomGame.Pictures.PortGraph.smooth_wireConnected_iff
#check ThomGame.Pictures.Smoothing.exists_without_junctions
#check ThomGame.Pictures.Smoothing.hubLabel
#check ThomGame.Pictures.Smoothing.hubFlip
#check ThomGame.Pictures.Smoothing.sign
#check ThomGame.Pictures.Smoothing.joint_card
#check ThomGame.Pictures.Smoothing.edge_card
#check ThomGame.Pictures.Smoothing.terminal_surjective
#check ThomGame.Pictures.Smoothing.wire_iff_final_edge
#check ThomGame.Pictures.Smoothing.terminalEquiv
#check ThomGame.Pictures.Smoothing.terminalPairing_edge_iff
#check ThomGame.Pictures.Smoothing.terminalPairing_independent
#check ThomGame.Pictures.Smoothing.unique_other_terminal
#check ThomGame.Pictures.Diagram.exists_smoothed_graph
#check ThomGame.SolutionGroup.word_eq_iff_smoothed_graph
#check ThomGame.Construction.smoothed_sigma_sign
#check ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_smoothed_graph
#print ThomGame.Pictures.FiniteReturn.Advances
#print ThomGame.Pictures.PortGraph.CircuitHasTerminal
#print ThomGame.Pictures.PortGraph.ribbonEuler
#check ThomGame.Pictures.FiniteReturn.Advances.sameCycle_iff
#check ThomGame.Pictures.FiniteReturn.Advances.orbitMap_injective
#check ThomGame.Pictures.PortGraph.smooth_circuit_advances
#check ThomGame.Pictures.PortGraph.smooth_sameCycle_iff
#check ThomGame.Pictures.PortGraph.smoothCircuitMap_injective
#check ThomGame.Pictures.PortGraph.smoothCircuitMap_surjective_of_not_loop
#check ThomGame.Pictures.PortGraph.loop_circuits_ne
#check ThomGame.Pictures.PortGraph.smoothCircuitMap_range_of_loop
#check ThomGame.Pictures.PortGraph.smooth_circuit_card
#check ThomGame.Pictures.PortGraph.smooth_ribbonEuler
#check ThomGame.Pictures.Smoothing.sameCircuit_iff
#check ThomGame.Pictures.Smoothing.circuit_card
#check ThomGame.Pictures.Smoothing.ribbonEuler
#check ThomGame.Pictures.Smoothing.portRotation
#check ThomGame.Pictures.Smoothing.terminalCircuitStep_independent
#check ThomGame.Pictures.Smoothing.circuitEmbedding_range_iff
#check ThomGame.Pictures.Smoothing.retainedCircuitEquiv
#check ThomGame.Pictures.Smoothing.discarded_circuit_card
#check ThomGame.Pictures.Smoothing.circles_length_independent
#check ThomGame.Construction.smoothed_sigma_circuit_card
#check ThomGame.Construction.smoothed_sigma_ribbonEuler
#check ThomGame.Construction.smoothed_sigma_circuit_range
#print ThomGame.Pictures.CycleSurgery.splice
#print ThomGame.Pictures.PortGraph.seamPermutation
#print ThomGame.Pictures.PortGraph.seamCircuit
#print ThomGame.Pictures.PortGraph.seamSplits
#print ThomGame.Pictures.MarkedReturn.time
#print ThomGame.Pictures.MarkedReturn.perm
#print ThomGame.Pictures.MarkedReturn.Hit
#print ThomGame.Pictures.PortGraph.IsBoundary
#print ThomGame.Pictures.PortGraph.boundaryNext
#print axioms ThomGame.Pictures.CycleSurgery.sameCycle_splice_iff
#print axioms ThomGame.Pictures.CycleSurgery.orbit_card_splice
#print axioms ThomGame.Pictures.PortGraph.comp_circuit_card
#print axioms ThomGame.Pictures.MarkedReturn.perm_preserved
#print axioms ThomGame.Pictures.PortGraph.smooth_boundaryNext
#print axioms ThomGame.Pictures.Smoothing.boundaryNext
#print axioms ThomGame.Construction.smoothed_sigma_boundaryNext
#check ThomGame.Pictures.CycleSurgery.joins
#check ThomGame.Pictures.CycleSurgery.separates
#check ThomGame.Pictures.CycleSurgery.joinedOrbitEquiv
#check ThomGame.Pictures.CycleSurgery.orbit_card_join
#check ThomGame.Pictures.CycleSurgery.orbit_card_split
#check ThomGame.Pictures.FiniteReturn.orbitEquiv
#check ThomGame.Pictures.FiniteReturn.sumOrbitEquiv
#check ThomGame.Pictures.PortGraph.circuitStep_compPorts
#check ThomGame.Pictures.PortGraph.circuitStep_tensorPorts
#check ThomGame.Pictures.PortGraph.tensorCircuitEquiv
#check ThomGame.Pictures.PortGraph.tensor_circuit_card
#check ThomGame.Pictures.PortGraph.seamPermutation_all
#check ThomGame.Pictures.PortGraph.seamPermutation_eq_of_mem_iff
#check ThomGame.Pictures.PortGraph.seamCircuit_all
#check ThomGame.Pictures.PortGraph.seamCircuit_sameCycle_iff
#check ThomGame.Pictures.PortGraph.seam_circuit_card
#check ThomGame.Pictures.PortGraph.singleton_seam_circuit_card
#check ThomGame.Pictures.PortGraph.seamSplits_perm
#check ThomGame.Pictures.MarkedReturn.time_pos
#check ThomGame.Pictures.MarkedReturn.before_time_not_mem
#check ThomGame.Pictures.MarkedReturn.time_eq_of_first
#check ThomGame.Pictures.MarkedReturn.next_injective
#check ThomGame.Pictures.MarkedReturn.sameCycle_iff
#check ThomGame.Pictures.MarkedReturn.markedOrbitEquiv
#check ThomGame.Pictures.MarkedReturn.Hit.unique
#check ThomGame.Pictures.MarkedReturn.hit_perm
#check ThomGame.Pictures.MarkedReturn.perm_preserved_of_commutes
#check ThomGame.Pictures.PortGraph.boundaryNext_return
#check ThomGame.Pictures.PortGraph.boundaryNext_first
#check ThomGame.Pictures.PortGraph.boundaryNext_sameCycle_iff
#check ThomGame.Pictures.PortGraph.boundaryNext_identity_top
#check ThomGame.Pictures.PortGraph.boundaryNext_identity_bottom
#check ThomGame.Pictures.PortGraph.boundaryNext_cap
#check ThomGame.Pictures.PortGraph.boundaryNext_cup
#check ThomGame.Pictures.PortGraph.boundaryNext_down
#check ThomGame.Pictures.PortGraph.boundaryNext_up
#check ThomGame.Pictures.PortGraph.boundaryNext_tensor_left
#check ThomGame.Pictures.PortGraph.boundaryNext_tensor_right
#check ThomGame.Pictures.Smoothing.boundaryNext_pow
#print ThomGame.Pictures.PortGraph.boundarySeamSwap
#print ThomGame.Pictures.PortGraph.IsOuter
#print ThomGame.Pictures.PortGraph.verticalBoundaryNext
#print axioms ThomGame.Pictures.PortGraph.boundaryNext_comp
#check ThomGame.Pictures.MarkedReturn.Hit.append
#check ThomGame.Pictures.MarkedReturn.Hit.twist_targets
#check ThomGame.Pictures.MarkedReturn.perm_preserved_of_paths
#check ThomGame.Pictures.PortGraph.boundarySeam_hit
#check ThomGame.Pictures.PortGraph.boundaryNext_comp_congr
#print ThomGame.Pictures.CircularPartition.Follows
#print ThomGame.Pictures.CircularPartition.NonInterlacing
#print ThomGame.Pictures.CircularPartition.OrderedNoncrossing
#print ThomGame.Pictures.PortGraph.boundaryOrderIndex
#print ThomGame.Pictures.PortGraph.boundaryCyclic
#print ThomGame.Pictures.PortGraph.boundaryBetween
#print ThomGame.Pictures.PortGraph.BoundaryNoncrossing
#print axioms ThomGame.Pictures.MarkedReturn.perm_nested
#print axioms ThomGame.Pictures.CircularPartition.OrderedNoncrossing.restrict
#print axioms ThomGame.Pictures.CircularPartition.NonInterlacing.arc_invariant
#print axioms ThomGame.Pictures.PortGraph.boundaryNoncrossing_identity
#print axioms ThomGame.Pictures.PortGraph.boundaryNoncrossing_down
#print axioms ThomGame.Pictures.PortGraph.boundaryNoncrossing_up
#print axioms ThomGame.Construction.smoothed_sigma_boundaryNoncrossing_iff
#check ThomGame.Pictures.MarkedReturn.perm_eq_of_pred_iff
#check ThomGame.Pictures.CircularPartition.Follows.expand_return
#check ThomGame.Pictures.CircularPartition.Follows.restrict
#check ThomGame.Pictures.CircularPartition.Follows.unique
#check ThomGame.Pictures.CircularPartition.NonInterlacing.restrict
#check ThomGame.Pictures.CircularPartition.OrderedNoncrossing.transport
#check ThomGame.Pictures.CircularPartition.noninterlacing_iff_arc_invariant
#check ThomGame.Pictures.CircularPartition.involutive_sameCycle
#check ThomGame.Pictures.CircularPartition.follows_involution
#check ThomGame.Pictures.CircularPartition.reflection_orderedNoncrossing
#check ThomGame.Pictures.CircularPartition.rotation_orderedNoncrossing
#check ThomGame.Pictures.PortGraph.boundaryCyclic_sameCycle
#check ThomGame.Pictures.PortGraph.boundaryNoncrossing_of_numbered
#check ThomGame.Pictures.PortGraph.boundaryNoncrossing_no_alternating
#check ThomGame.Pictures.PortGraph.numberedBoundaryNext_identity
#check ThomGame.Pictures.PortGraph.boundaryNoncrossing_cap
#check ThomGame.Pictures.PortGraph.boundaryNoncrossing_cup
#check ThomGame.Pictures.Smoothing.boundaryNoncrossing_iff
#print ThomGame.Pictures.PortGraph.tensorBoundaryEquiv
#print ThomGame.Pictures.PortGraph.numberedTensorIndex
#print axioms ThomGame.Pictures.FinCircle.hit_image_next
#print axioms ThomGame.Pictures.CircularPartition.orderedNoncrossing_combine
#print axioms ThomGame.Pictures.PortGraph.boundaryNoncrossing_tensor
#check ThomGame.Pictures.FinCircle.hit_of_lt
#check ThomGame.Pictures.FinCircle.hit_to_zero
#check ThomGame.Pictures.FinCircle.hit_wrap
#check ThomGame.Pictures.CircularPartition.strictMono_sbtw
#check ThomGame.Pictures.CircularPartition.follows_combine
#check ThomGame.Pictures.CircularPartition.noninterlacing_combine_source
#check ThomGame.Pictures.PortGraph.numberedBoundaryNext_noncrossing
#check ThomGame.Pictures.PortGraph.numberedTensorIndex_left_val
#check ThomGame.Pictures.PortGraph.numberedTensorIndex_right_val
#check ThomGame.Pictures.PortGraph.numberedTensorIndex_left_strictMono
#check ThomGame.Pictures.PortGraph.numberedTensorIndex_right_strictMono
#check ThomGame.Pictures.PortGraph.numberedTensorIndex_not_alternating_left
#check ThomGame.Pictures.PortGraph.numberedTensorIndex_not_alternating_right
#check ThomGame.Pictures.PortGraph.numberedBoundaryNext_tensor_index
#print ThomGame.Pictures.CycleSurgery.isolate
#print ThomGame.Pictures.CircularPartition.subsetEnumeration
#print ThomGame.Pictures.CircularPartition.renumber
#print axioms ThomGame.Pictures.CycleSurgery.sameCycle_join_iff
#print axioms ThomGame.Pictures.CycleSurgery.perm_splice_of_apply
#print axioms ThomGame.Pictures.CircularPartition.NonInterlacing.splice_restrict_of_arc_iff
#print axioms ThomGame.Pictures.FinCircle.hit_iff_no_between
#print axioms ThomGame.Pictures.CircularPartition.OrderedNoncrossing.follows_isolate_splice
#print axioms ThomGame.Pictures.CircularPartition.OrderedNoncrossing.splice_restrict_adjacent
#print axioms ThomGame.Pictures.CircularPartition.OrderedNoncrossing.splice_restrict_renumber
#print axioms ThomGame.Pictures.MarkedReturn.perm_splice_retained
#check ThomGame.Pictures.CycleSurgery.splice_fixed_of_apply
#check ThomGame.Pictures.CycleSurgery.splice_hit_of_apply
#check ThomGame.Pictures.CycleSurgery.expand_splice_hit_of_apply
#check ThomGame.Pictures.CycleSurgery.perm_isolate
#check ThomGame.Pictures.CycleSurgery.sameCycle_isolate_away_iff
#check ThomGame.Pictures.CircularPartition.Follows.apply_of_adjacent
#check ThomGame.Pictures.CircularPartition.OrderedNoncrossing.splice_restrict_sameCycle
#check ThomGame.Pictures.CircularPartition.NonInterlacing.arc_join_iff
#check ThomGame.Pictures.CircularPartition.adjacent_arc_iff
#check ThomGame.Pictures.CircularPartition.NonInterlacing.splice_restrict_adjacent
#check ThomGame.Pictures.FinCircle.hit_of_no_between
#check ThomGame.Pictures.FinCircle.no_between_of_hit
#check ThomGame.Pictures.CircularPartition.Follows.no_between
#check ThomGame.Pictures.CircularPartition.follows_of_no_between
#check ThomGame.Pictures.CircularPartition.increasing_return
#check ThomGame.Pictures.CircularPartition.subsetEnumeration_strictMono
#check ThomGame.Pictures.CircularPartition.subsetEnumeration_return
#check ThomGame.Pictures.CircularPartition.OrderedNoncrossing.renumber
#print ThomGame.Pictures.MarkedReturn.nestedSubset
#print ThomGame.Pictures.PortGraph.seamOrderIndex
#print ThomGame.Pictures.PortGraph.partialBoundarySwap
#print ThomGame.Pictures.PortGraph.SeamRemaining
#print ThomGame.Pictures.PortGraph.numberedPartialSeam
#print ThomGame.Pictures.PortGraph.outerSeamNumbering
#print axioms ThomGame.Pictures.MarkedReturn.perm_subtypeEquiv
#print axioms ThomGame.Pictures.MarkedReturn.perm_nested_subset
#print axioms ThomGame.Pictures.CircularPartition.OrderedNoncrossing.splice_restrict_nested
#print axioms ThomGame.Pictures.PortGraph.partialBoundarySwap_step
#print axioms ThomGame.Pictures.PortGraph.retainedSeam_adjacent
#print axioms ThomGame.Pictures.PortGraph.numberedPartialSeam_noncrossing
#print axioms ThomGame.Pictures.PortGraph.boundaryNoncrossing_comp
#print axioms ThomGame.Pictures.Diagram.graph_boundaryNoncrossing
#print axioms ThomGame.Construction.smoothed_sigma_boundaryNoncrossing
#check ThomGame.Pictures.CircularPartition.OrderedNoncrossing.splice_restrict_numbered
#check ThomGame.Pictures.CircularPartition.orderedNoncrossing_consecutive
#check ThomGame.Pictures.PortGraph.seamOrderIndex_top_val
#check ThomGame.Pictures.PortGraph.seamOrderIndex_left_val
#check ThomGame.Pictures.PortGraph.seamOrderIndex_right_val
#check ThomGame.Pictures.PortGraph.seamOrderIndex_bottom_val
#check ThomGame.Pictures.PortGraph.partialBoundarySwap_zero
#check ThomGame.Pictures.PortGraph.partialBoundarySwap_all
#check ThomGame.Pictures.PortGraph.numberedSeamRemaining_iff
#check ThomGame.Pictures.PortGraph.SeamRemaining_all
#check ThomGame.Pictures.PortGraph.numberedPartialSeam_step
#check ThomGame.Pictures.PortGraph.numberedPartialSeam_zero_noncrossing
#check ThomGame.Pictures.PortGraph.outerSeamNumbering_val
#check ThomGame.Pictures.PortGraph.outerSeamNumbering_strictMono
#check ThomGame.Pictures.PortGraph.outerSeamIndex_next
#check ThomGame.Pictures.PortGraph.outerSeamNumbering_next
#check ThomGame.Pictures.Smoothing.diagram_boundaryNoncrossing
#check ThomGame.Construction.sigmaDiagram_boundaryNoncrossing
#print ThomGame.Pictures.RibbonConnectivity.Connected
#print ThomGame.Pictures.RibbonConnectivity.Component
#print ThomGame.Pictures.PortGraph.Reachable
#print ThomGame.Pictures.PortGraph.GraphComponent
#print ThomGame.Pictures.RibbonConnectivity.SeesComponents
#print ThomGame.Pictures.PortGraph.BoundarySeesComponents
#print ThomGame.Pictures.RibbonConnectivity.eulerCount
#print ThomGame.Pictures.RibbonConnectivity.eulerDefect
#print axioms ThomGame.Pictures.PortGraph.connected_iff_vertex_reachable
#print axioms ThomGame.Pictures.RibbonConnectivity.connected_splice_iff
#print axioms ThomGame.Pictures.RibbonConnectivity.component_card_join
#print axioms ThomGame.Pictures.RibbonConnectivity.component_card_same
#print axioms ThomGame.Pictures.RibbonConnectivity.SeesComponents.splice_restrict
#print axioms ThomGame.Pictures.RibbonConnectivity.eulerDefect_leaf_splice
#print axioms ThomGame.Pictures.PortGraph.boundarySeesComponents_tensor
#print axioms ThomGame.Pictures.PortGraph.eulerCount_eq_ribbonEuler
#print axioms ThomGame.Construction.sigmaGraph_component_card
#print axioms ThomGame.Construction.sigmaGraph_eulerDefect
#check ThomGame.Pictures.RibbonConnectivity.connected_congr
#check ThomGame.Pictures.RibbonConnectivity.sameCycle_connected
#check ThomGame.Pictures.RibbonConnectivity.seam_connected
#check ThomGame.Pictures.RibbonConnectivity.old_connected_splice
#check ThomGame.Pictures.RibbonConnectivity.joinedComponentEquiv
#check ThomGame.Pictures.RibbonConnectivity.sameCycle_splice_marked_next
#check ThomGame.Pictures.RibbonConnectivity.Leaves.splice_restrict
#check ThomGame.Pictures.RibbonConnectivity.SeesComponents.sum
#check ThomGame.Pictures.RibbonConnectivity.not_connected_sum
#check ThomGame.Pictures.RibbonConnectivity.rotation_card_leaf_splice
#check ThomGame.Pictures.RibbonConnectivity.eulerCount_leaf_splice
#check ThomGame.Pictures.PortGraph.connected_of_same_vertex
#check ThomGame.Pictures.PortGraph.boundary_sameCycle_reachable
#check ThomGame.Pictures.PortGraph.boundary_leaves
#check ThomGame.Pictures.PortGraph.boundarySeesComponents_reachable
#check ThomGame.Pictures.PortGraph.boundarySeesComponents_identity
#check ThomGame.Pictures.PortGraph.boundarySeesComponents_cap
#check ThomGame.Pictures.PortGraph.boundarySeesComponents_cup
#check ThomGame.Pictures.PortGraph.boundarySeesComponents_down
#check ThomGame.Pictures.PortGraph.boundarySeesComponents_up
#check ThomGame.Pictures.PortGraph.dartComponentMap_injective
#check ThomGame.Pictures.PortGraph.dartComponentEquiv
#check ThomGame.Pictures.PortGraph.rotationVertexEquiv
#check ThomGame.Pictures.PortGraph.edgeOrbitEquiv
#check ThomGame.Pictures.PortGraph.eulerDefect_eq_ribbonEuler
#check ThomGame.Construction.sigmaGraph_eulerCount
#print ThomGame.Pictures.PortGraph.partialDartSwap
#print ThomGame.Pictures.PortGraph.FullSeamRemaining
#print ThomGame.Pictures.PortGraph.fullPartialSeam
#print ThomGame.Pictures.PortGraph.numberedFullBoundary
#print axioms ThomGame.Pictures.PortGraph.fullPartialSeam_boundary_hit
#print axioms ThomGame.Pictures.PortGraph.numberedFullBoundary_next
#print axioms ThomGame.Pictures.PortGraph.fullPartialSeam_next_of_sameCycle
#print axioms ThomGame.Pictures.PortGraph.fullPartialSeam_seesComponents
#print axioms ThomGame.Pictures.PortGraph.boundarySeesComponents_comp
#print axioms ThomGame.Pictures.Diagram.graph_boundarySeesComponents
#print axioms ThomGame.Pictures.RibbonConnectivity.eulerDefect_congr
#print axioms ThomGame.Pictures.RibbonConnectivity.eulerDefect_sum
#print axioms ThomGame.Pictures.PortGraph.eulerDefect_comp
#print axioms ThomGame.Pictures.PortGraph.eulerDefect_down
#print axioms ThomGame.Pictures.PortGraph.eulerDefect_up
#print axioms ThomGame.Pictures.Diagram.graph_eulerDefect
#print axioms ThomGame.Construction.sigmaDiagram_ribbonEuler
#print axioms ThomGame.Pictures.PortGraph.smooth_connected_iff
#print axioms ThomGame.Pictures.Smoothing.connected_iff
#print axioms ThomGame.Construction.smoothed_sigma_boundarySeesComponents
#check ThomGame.Pictures.PortGraph.partialDartSwap_step
#check ThomGame.Pictures.PortGraph.fullPartialSeam_all
#check ThomGame.Pictures.PortGraph.fullPartialSeam_leaves
#check ThomGame.Pictures.PortGraph.remainingBoundaryPorts_next
#check ThomGame.Pictures.PortGraph.numberedFullBoundary_sameCycle
#check ThomGame.Pictures.Diagram.graph_boundary_reachable_iff
#check ThomGame.Pictures.RibbonConnectivity.componentCongrEquiv
#check ThomGame.Pictures.RibbonConnectivity.sumComponentEquiv
#check ThomGame.Pictures.PortGraph.fullPartialSeam_eulerDefect
#check ThomGame.Pictures.PortGraph.eulerDefect_tensor
#check ThomGame.Pictures.RibbonConnectivity.eulerDefect_of_empty
#check ThomGame.Pictures.PortGraph.eulerDefect_of_no_internal
#check ThomGame.Pictures.Diagram.graph_ribbonEuler
#check ThomGame.Construction.sigmaDiagram_eulerDefect
#check ThomGame.Construction.sigmaDiagram_ribbonEuler
#check ThomGame.Pictures.PortGraph.smooth_boundarySeesComponents_iff
#check ThomGame.Pictures.Smoothing.reachable_iff
#check ThomGame.Pictures.Smoothing.boundarySeesComponents_iff
#print ThomGame.Hypergraph.GeneralizedHom
#print ThomGame.Hypergraph.OpenEmbedding
#print ThomGame.Hypergraph.Retraction
#print ThomGame.Hypergraph.Cycle
#print ThomGame.Hypergraph.Cycle.SunNeighbourhood
#print ThomGame.Hypergraph.Cycle.Stellar
#print axioms ThomGame.Pictures.PortGraph.smoothComponentMap_injective
#print axioms ThomGame.Pictures.PortGraph.loop_connected_iff
#print axioms ThomGame.Pictures.PortGraph.smoothComponentComplementEquiv
#print axioms ThomGame.Pictures.PortGraph.smoothComponentEquiv
#print axioms ThomGame.Pictures.PortGraph.smooth_dartComponent_card
#print axioms ThomGame.Pictures.PortGraph.smooth_graphComponent_card
#print axioms ThomGame.Pictures.Smoothing.graphComponent_card
#print axioms ThomGame.Pictures.Smoothing.graphEulerDefect
#print axioms ThomGame.Pictures.Smoothing.diagram_ribbonEuler
#print axioms ThomGame.Pictures.Smoothing.componentMap_range_iff
#print axioms ThomGame.Pictures.Smoothing.retainedComponentEquiv
#print axioms ThomGame.Pictures.Smoothing.discarded_component_card
#print axioms ThomGame.Construction.smoothed_sigma_graphComponent_card
#print axioms ThomGame.Construction.smoothed_sigma_eulerDefect
#print axioms ThomGame.Construction.smoothed_sigma_ribbonEuler_eq_components
#print axioms ThomGame.Hypergraph.GeneralizedHom.retained_matrix
#print axioms ThomGame.Hypergraph.GeneralizedHom.deleted_matrix_even
#print axioms ThomGame.Hypergraph.GeneralizedHom.deleted_edge_images
#print axioms ThomGame.SparseSystem.hypergraph_matrix
#print axioms ThomGame.SparseSystem.hypergraph_incidence_nodup
#print axioms ThomGame.SparseSystem.hypergraph_multiplicity_eq_ite
#print axioms ThomGame.Wheel.Family.centralRetraction
#print axioms ThomGame.Wheel.Family.central_rim_incident
#print axioms ThomGame.Wheel.Family.centralCycle
#print axioms ThomGame.Wheel.Family.centralStellar
#print axioms ThomGame.Hypergraph.Cycle.endpoints_distinct
#print axioms ThomGame.Hypergraph.Cycle.edge_eq_of_endpoints
#print axioms ThomGame.Hypergraph.Cycle.closed
#print axioms ThomGame.Hypergraph.Cycle.rim_degree
#print axioms ThomGame.Hypergraph.Cycle.connected
#print axioms ThomGame.Hypergraph.Cycle.SunNeighbourhood.edge_iff
#print axioms ThomGame.Hypergraph.Cycle.Stellar.neighbourhood_edge_iff
#print axioms ThomGame.Hypergraph.Cycle.Stellar.cubic
#print axioms ThomGame.Construction.centralWheelStellar
#print axioms ThomGame.Construction.numberedCentralWheelStellar
#print axioms ThomGame.Wheel.Family.aux_incident
#print axioms ThomGame.Wheel.Family.pentagonCycle
#print axioms ThomGame.Wheel.Family.pentagonSunNeighbourhood
#print axioms ThomGame.Construction.numberedPentagonWheelCycle
#print axioms ThomGame.Construction.numberedPentagonWheelSunNeighbourhood
#print axioms ThomGame.Pictures.Diagram.charge_balance
#print axioms ThomGame.Pictures.Pairing.sum_charge
#print axioms ThomGame.Pictures.PortGraph.charge_balance
#print axioms ThomGame.Pictures.PortGraph.sign_eq_character
#print axioms ThomGame.Pictures.Diagram.graph_character
#print axioms ThomGame.Pictures.Smoothing.character
#print axioms ThomGame.Pictures.sunPresentation_incidence
#print axioms ThomGame.Pictures.Diagram.sun_character
#print axioms ThomGame.Pictures.Diagram.closed_sun_character
#print axioms ThomGame.Pictures.Diagram.closed_sun_sign
#print axioms ThomGame.Pictures.PortGraph.sun_character
#print axioms ThomGame.Pictures.PortGraph.closed_sun_character
#print axioms ThomGame.Pictures.PortGraph.closed_sun_sign
#check ThomGame.Hypergraph.Retraction.congrSource
#check ThomGame.Hypergraph.Retraction.reindexSource
#check ThomGame.Hypergraph.OpenEmbedding.congrTarget
#check ThomGame.Hypergraph.OpenEmbedding.reindexTarget
#print ThomGame.Hypergraph.Constellation
#print ThomGame.Pictures.Relabelling
#print axioms ThomGame.CyclicParity.prefix_next
#print axioms ThomGame.CyclicChain.get_next
#print axioms ThomGame.PentagonFold.local_valid
#print axioms ThomGame.Wheel.Family.fold_row_images
#print axioms ThomGame.Wheel.Family.foldRetraction
#print axioms ThomGame.Construction.wheelFoldPhase
#print axioms ThomGame.Construction.wheel_letters_ne_next
#print axioms ThomGame.Construction.pentagonWheelRetraction
#print axioms ThomGame.Construction.numberedPentagonWheelRetraction
#print axioms ThomGame.Construction.pentagonWheelStellar
#print axioms ThomGame.Construction.numberedPentagonWheelStellar
#print axioms ThomGame.Construction.oddPentagon_not_stellar
#print axioms ThomGame.Wheel.Family.a_mem_pentagon
#print axioms ThomGame.Wheel.Family.central_pentagon_intersection
#print axioms ThomGame.Wheel.Family.pentagon_intersection_unique
#print axioms ThomGame.Hypergraph.Constellation.edge_range_injective
#print axioms ThomGame.Hypergraph.Constellation.withAllStellar
#print axioms ThomGame.Construction.wheelCycle_stellar_of_ne_odd
#print axioms ThomGame.Construction.wheelCycle_eq_odd_of_not_stellar
#print axioms ThomGame.Construction.pentagon_private_edge
#print axioms ThomGame.Construction.wheelCycles_intersection_unique
#print axioms ThomGame.Construction.oddWheelCycle_covered
#print axioms ThomGame.Construction.wheelConstellation
#print axioms ThomGame.Construction.homogeneousWheelConstellation
#print axioms ThomGame.Hypergraph.Cycle.exists_other_incident
#print axioms ThomGame.Hypergraph.Cycle.SunNeighbourhood.incidence_eq
#print axioms ThomGame.Hypergraph.Cycle.SunNeighbourhood.spoke_not_mem_cycle
#print axioms ThomGame.Hypergraph.Constellation.spoke_mem_of_shared
#print axioms ThomGame.Hypergraph.Constellation.eq_or_eq_of_mem
#print axioms ThomGame.Hypergraph.Constellation.containing_card_le_two
#print axioms ThomGame.Hypergraph.Constellation.restrict
#print axioms ThomGame.Pictures.Diagram.rotateDown
#print axioms ThomGame.Pictures.Diagram.reverseDown
#print axioms ThomGame.Pictures.Diagram.exists_permuted_triangle
#print axioms ThomGame.Pictures.Diagram.exists_empty_of_even_monochromatic
#print axioms ThomGame.Pictures.Relabelling.diagram
#print axioms ThomGame.Pictures.Relabelling.labels_diagram_perm
#print axioms ThomGame.Pictures.Relabelling.size_diagram_le
#print axioms ThomGame.Pictures.Relabelling.sign_diagram
#print axioms ThomGame.Pictures.exists_relation_image
#print axioms ThomGame.Pictures.Relabelling.ofGeneralizedHom
#print axioms ThomGame.Hypergraph.GeneralizedHom.postcomposeEmbedding
#print axioms ThomGame.Hypergraph.Retraction.endomorphism_edge
#print axioms ThomGame.Pictures.retraction_filterMap
#print axioms ThomGame.Pictures.retractDiagram
#print axioms ThomGame.Pictures.retractDiagram_size_le
#print axioms ThomGame.Pictures.retractDiagram_labels_mem
#print axioms ThomGame.Pictures.retractDiagram_sign_zero
#print axioms ThomGame.Pictures.retractDiagram_minimal
#print axioms ThomGame.Construction.numberedWheelCycleRetraction
#print axioms ThomGame.Construction.sigmaToCycleSun
#print axioms ThomGame.Construction.sigmaToCycleSun_closed_character
#print axioms ThomGame.Construction.retractSigmaDiagram_size_le
#print axioms ThomGame.Construction.retractSigmaDiagram_sign_zero
#print axioms ThomGame.Construction.retractSigmaDiagram_minimal
#print axioms ThomGame.Hypergraph.Cycle.row_rim_indices
#print axioms ThomGame.Hypergraph.Cycle.row_rim_card
#print ThomGame.Pictures.PortGraph.RimDart
#print ThomGame.Pictures.PortGraph.RimIncident
#print axioms ThomGame.Pictures.PortGraph.rimPairing
#print axioms ThomGame.Pictures.PortGraph.rimEdgeToEdge_injective
#print axioms ThomGame.Pictures.PortGraph.rimIncidentEquiv
#print axioms ThomGame.Pictures.PortGraph.rimIncident_card
#print axioms ThomGame.Pictures.PortGraph.existsUnique_rim_neighbour
#print axioms ThomGame.Pictures.PortGraph.rimSwitch_involutive
#print axioms ThomGame.Pictures.PortGraph.rimVertexPairing_eq_iff
#print axioms ThomGame.Pictures.PortGraph.rimWalk_vertex
#print axioms ThomGame.Pictures.PortGraph.rimComponent_twin
#print axioms ThomGame.Pictures.PortGraph.rimComponent_vertex
#print axioms ThomGame.Construction.numberedWheelCycles
#print axioms ThomGame.Construction.closed_sigma_rimIncident_card
#print axioms ThomGame.Construction.closedSigmaRimWalk_vertex
#print axioms ThomGame.Pictures.PairingCycles.not_sameCycle_edge
#print axioms ThomGame.Pictures.PairingCycles.not_sameCycle_vertex
#print axioms ThomGame.Pictures.PairingCycles.reverse_sameCycle
#print axioms ThomGame.Pictures.PairingCycles.edge_injective_on_orbit
#print axioms ThomGame.Pictures.PairingCycles.vertex_injective_on_orbit
#print axioms ThomGame.Pictures.PairingCycles.connected_iff
#print axioms ThomGame.Pictures.OrbitEnumeration.dart_range
#print axioms ThomGame.Pictures.OrbitEnumeration.dart_next
#print axioms ThomGame.Pictures.PairingCycles.componentEquiv
#print axioms ThomGame.Pictures.PairingCycles.pairedDart_twin
#print axioms ThomGame.Pictures.PairingCycles.pairedDart_vertex_true
#print axioms ThomGame.Pictures.PairingCycles.pairedDart_vertex_false
#print ThomGame.Pictures.PortGraph.SimpleCircuit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.incoming_vertex
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.incoming_ne_outgoing
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_component_darts
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_vertex_complete
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_edge_complete
#print axioms ThomGame.Construction.closedSigmaRimCircuit
#print axioms ThomGame.Construction.closedSigmaRimCircuit_vertex_complete
#print axioms ThomGame.Construction.closedSigmaRimCircuit_edge_complete
#print axioms ThomGame.Pictures.RibbonConnectivity.connected_splice_iff_of_seam
#print axioms ThomGame.Pictures.RibbonConnectivity.component_card_join_of_fixed
#print axioms ThomGame.Pictures.RibbonConnectivity.component_card_same_of_fixed
#print ThomGame.Pictures.RotationEuler.count
#print axioms ThomGame.Pictures.RotationEuler.count_splice
#print axioms ThomGame.Pictures.RotationEuler.removed_pair_involutive
#print axioms ThomGame.Pictures.RotationEuler.count_le_twice_components
#print axioms ThomGame.Pictures.RotationEuler.rotationComponentEquiv
#print axioms ThomGame.Pictures.RotationEuler.dualComponentEquiv
#print axioms ThomGame.Pictures.RotationEuler.dual_count
#print axioms ThomGame.Pictures.PortGraph.rotationEuler_eq_eulerCount
#print axioms ThomGame.Pictures.PortGraph.dualEuler_eq_eulerCount
#print axioms ThomGame.Pictures.PortGraph.eulerDefect_nonpos
#print axioms ThomGame.Pictures.PortGraph.ribbonEuler_le_twice_components
#print axioms ThomGame.Pictures.MarkedReturn.perm_mul_retained
#print axioms ThomGame.Pictures.MarkedReturn.avoids_mul_iff
#print axioms ThomGame.Pictures.MarkedReturn.unmarkedOrbitEquiv
#print axioms ThomGame.Pictures.MarkedReturn.orbit_card_mul_balance
#print axioms ThomGame.Pictures.CircuitPermutations.eq_vertex_of_cycles
#print axioms ThomGame.Pictures.CircuitPermutations.vertex_orbit_card
#print axioms ThomGame.Pictures.CircuitPermutations.edge_orbit_card
#print axioms ThomGame.Pictures.CircuitPermutations.sides_sameCycle
#print axioms ThomGame.Pictures.CircuitPermutations.sides_orbit_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.portEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_twin_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.rotation_return_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.pairing_return_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.edgeTwist_involutive
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutPairing_involutive
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.twisted_rotation_orbit_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutPairing_orbit_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutFaceOrbitEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_euler_count
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_components_increase
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_marked_connected_of_side
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reclosed_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_component_card_cases
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_component_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_sides_separate
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.old_connected_base_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_connected_iff_outside
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_marked_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutComponentToOld
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sideComponent_range
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutSidesEquiv
#print axioms ThomGame.Pictures.Diagram.graph_dualEuler
#print axioms ThomGame.Pictures.Diagram.cut_component_card
#print axioms ThomGame.Pictures.Smoothing.diagram_cut_component_card
#print axioms ThomGame.Construction.closedSigmaRimDiagram_cut_component_card
#print axioms ThomGame.Construction.closedSigmaRimDiagram_cut_marked_connected_iff
#print axioms ThomGame.Construction.closedSigmaRimDiagram_sidesEquiv
#print axioms ThomGame.Construction.smoothed_closedSigmaRim_cut_component_card
#print axioms ThomGame.Construction.smoothed_closedSigmaRim_cut_marked_connected_iff
#print axioms ThomGame.Construction.smoothed_closedSigmaRim_sidesEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.onCircuitVertex_iff_sector
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sector_unique
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_connected_same_vertex
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.onSide_twin_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sector_frontier_iff
#print axioms ThomGame.Pictures.OrbitEnumeration.retainedEnumeration
#print axioms ThomGame.Pictures.OrbitEnumeration.retainedEnumeration_return
#print axioms ThomGame.Pictures.OrbitEnumeration.retainedList_nodup
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.frontierEnumeration_return
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.frontier_unique
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_frontier_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundaryEnumeration_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.mem_frontierDarts_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.keptPairing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.interior_port_kept
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPortMap_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPortMap_injective
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPortMap_inv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_hub_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_joint_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_character
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_charge_balance
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.component_vertex_partition
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.interiorVertex_side_unique
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.component_hub_sum
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.component_hub_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_sign_partition
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_character_partition
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_marked_iff
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_frontier_not_rim
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_frontierWord_no_rim
#print axioms ThomGame.Construction.closedSigmaRimFrontierWord_no_rim
#print axioms ThomGame.Construction.closedSigmaRimRegionGraph
#print axioms ThomGame.Construction.closedSigmaRimRegionPorts
#print axioms ThomGame.Construction.closedSigmaRimRegionGraph_twin
#print axioms ThomGame.Construction.closedSigmaRimRegionGraph_character
#print axioms ThomGame.Construction.smoothedSigmaRimRegionGraph
#print axioms ThomGame.Construction.smoothedSigmaRimRegionPorts
#print axioms ThomGame.Construction.smoothedSigmaRimRegionGraph_twin
#print axioms ThomGame.Pictures.Port.bottomPorts
#print axioms ThomGame.Pictures.PortGraph.selectedPorts
#print axioms ThomGame.Pictures.Pairing.copies
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_vertex_port_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germOriginalEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germRawPairing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_twin_internal_uncut
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_twin_internal_outward
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_twin_bottom
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_hub_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_hub_sum
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_hub_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_region_hub_sum
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_pair_hub_sum
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_character
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_sign
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_region_character
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_pair_sign
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_germGraph_sign_zero
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_charge_balance
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluingSeamTurn_involutive
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluingRetained_iff_fixed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluingRetainedEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluing_original_hit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluing_firstReturn
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluingOriginal_partition
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluingComponentEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluingOriginal_twin_val
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedGraph
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedPorts_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedPorts_seam
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedPorts_step
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedRetained_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedComponentPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.glued_firstReturn
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.glued_firstReturn_val
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedGraph_sign
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedGraph_character
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_hub_label
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_stellar_sign
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_exists_germ_sign_zero
#print ThomGame.Pictures.PortGraph.OddRimComponentHasZeroSignGerm
#print axioms ThomGame.Pictures.PortGraph.stellar_oddRimComponentHasZeroSignGerm
#print axioms ThomGame.SolutionGroup.triangularPresentation_parity
#print axioms ThomGame.Construction.numberedWheelCycle_stellar_of_ne_odd
#print axioms ThomGame.Construction.closedSigmaRimGermGraph
#print axioms ThomGame.Construction.closedSigmaRimGermPorts
#print axioms ThomGame.Construction.closedSigmaRimGermGraph_twin
#print axioms ThomGame.Construction.closedSigmaRimGermGraph_character
#print axioms ThomGame.Construction.closedSigmaRimGermGraph_exists_sign_zero
#print axioms ThomGame.Construction.closedSigmaRimGluedGraph
#print axioms ThomGame.Construction.closedSigmaRimGluedGraph_sign
#print axioms ThomGame.Construction.closedSigmaRimGlued_firstReturn
#print axioms ThomGame.Construction.smoothedSigmaRimGermGraph
#print axioms ThomGame.Construction.smoothedSigmaRimGermGraph_exists_sign_zero
#print axioms ThomGame.Construction.smoothedSigmaRimGluedGraph
#print axioms ThomGame.Construction.smoothedSigmaRimGlued_firstReturn
#print axioms ThomGame.Pictures.MarkedReturn.Hit.sameCycle
#print axioms ThomGame.Pictures.PortGraph.selectedTurn_involutive
#print axioms ThomGame.Pictures.PortGraph.selectedTerminal_survives
#print axioms ThomGame.Pictures.PortGraph.smooth_selected_advances
#print axioms ThomGame.Pictures.PortGraph.smooth_selected_return
#print ThomGame.Pictures.PortGraph.SelectedAccessible
#print axioms ThomGame.Pictures.PortGraph.selected_not_loop
#print axioms ThomGame.Pictures.PortGraph.smooth_selectedAccessible
#print axioms ThomGame.Pictures.Smoothing.jointEmbedding
#print axioms ThomGame.Pictures.Smoothing.portEmbedding_joint
#print axioms ThomGame.Pictures.Smoothing.jointLabel
#print axioms ThomGame.Pictures.Smoothing.portRotation
#print ThomGame.Pictures.Smoothing.RemovesOnly
#print ThomGame.Pictures.Smoothing.ClearsSelected
#print axioms ThomGame.Pictures.Smoothing.selectedTerminal_iff
#print axioms ThomGame.Pictures.Smoothing.selectedTerminal_surjective
#print axioms ThomGame.Pictures.Smoothing.selectedReturn_preserved
#print axioms ThomGame.Pictures.Smoothing.selectedTerminalEquiv
#print axioms ThomGame.Pictures.Smoothing.selected_twin_return
#print axioms ThomGame.Pictures.Smoothing.exists_selected_without_circles
#print ThomGame.Pictures.SelectedReduction
#print axioms ThomGame.Pictures.PortGraph.reduceSelected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluing_accessible
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.glued_selectedAccessible
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.glued_firstReturn_component
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germReduction
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germReduction_return
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredPorts_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germReduction_sign
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germReduction_character
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedProjection_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedProjection_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredPorts_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredPorts_vertex_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredPorts_edge_iff
#print axioms ThomGame.Construction.closedSigmaRimReduction
#print axioms ThomGame.Construction.closedSigmaRecoveryTrace
#print axioms ThomGame.Construction.closedSigmaRecoveredPorts
#print axioms ThomGame.Construction.closedSigmaRecoveredPorts_twin
#print axioms ThomGame.Construction.closedSigmaRecoveredPorts_label
#print axioms ThomGame.Construction.closedSigmaRecoveredPorts_rotation
#print axioms ThomGame.Construction.closedSigmaRecoveredPorts_vertex_iff
#print axioms ThomGame.Construction.closedSigmaRecoveredGraph_sign
#print axioms ThomGame.Construction.smoothedSigmaRimReduction
#print axioms ThomGame.Construction.smoothedSigmaRecoveryTrace
#print axioms ThomGame.Construction.smoothedSigmaRecoveredPorts
#print axioms ThomGame.Construction.smoothedSigmaRecoveredPorts_twin
#print axioms ThomGame.Construction.smoothedSigmaRecoveredPorts_rotation
#print ThomGame.Pictures.PortGraph.Selection
#print axioms ThomGame.Pictures.selectPositions_append
#print axioms ThomGame.Pictures.PortGraph.Selection.comp_seam
#print axioms ThomGame.Pictures.Diagram.exists_selected
#print axioms ThomGame.Pictures.Diagram.selectedLabels_sublist
#print axioms ThomGame.Pictures.Diagram.sum_selectedLabels
#print axioms ThomGame.Pictures.Diagram.labels_select
#print axioms ThomGame.Pictures.Diagram.size_select
#print axioms ThomGame.Pictures.Diagram.sign_select
#print axioms ThomGame.Pictures.PortGraph.componentSelection
#print axioms ThomGame.Pictures.PortGraph.sum_componentWeight
#print axioms ThomGame.Pictures.PortGraph.exists_odd_component
#print axioms ThomGame.Pictures.Diagram.componentDiagram_weight
#print axioms ThomGame.Pictures.Diagram.minimal_odd_hubs_in_component
#print axioms ThomGame.Pictures.Diagram.minimal_odd_exists_component
#print axioms ThomGame.Pictures.Diagram.minimal_odd_hubs_reachable
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.inCircuitComponent_iff_reachable
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.inCircuitComponent_iff_graphComponent
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.component_hub_sum_of_connected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_sign_of_no_component_hubs
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_germ_sign_zero_of_hubs_reachable
#print axioms ThomGame.Pictures.Diagram.minimal_odd_circuit_exists_germ_sign_zero
#print axioms ThomGame.Pictures.Smoothing.hubs_reachable
#print axioms ThomGame.Pictures.Smoothing.minimal_odd_circuit_exists_germ_sign_zero
#print ThomGame.Pictures.PortGraph.RimHasZeroSignGerm
#print axioms ThomGame.Pictures.Diagram.minimal_odd_stellar_rim_hasZeroSignGerm
#print axioms ThomGame.Pictures.Smoothing.minimal_odd_stellar_rim_hasZeroSignGerm
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_odd_hubs_connected
#print axioms ThomGame.Construction.closedSigmaRimGermGraph_minimal_exists_sign_zero
#print axioms ThomGame.Construction.smoothedSigmaRimGermGraph_minimal_exists_sign_zero
#print axioms ThomGame.Pictures.PortGraph.closed_reachable_of_hubs
#print axioms ThomGame.Pictures.Smoothing.minimal_odd_reduced_reachable
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredAllPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredAllPorts_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredAllPorts_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredAllPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredAllPorts_vertex_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredAllPorts_edge_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germReduction_sign_of_connected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germReduction_character_of_connected
#print axioms ThomGame.Pictures.Smoothing.minimal_odd_recoveredAllPorts
#print axioms ThomGame.Construction.reduced_minimal_odd_sigma_reachable
#print axioms ThomGame.Construction.minimalSigmaRecoveredAllPorts
#print axioms ThomGame.Construction.minimalSigmaRecoveredAllPorts_twin
#print axioms ThomGame.Construction.minimalSigmaRecoveredAllPorts_label
#print axioms ThomGame.Construction.minimalSigmaRecoveredAllPorts_rotation
#print axioms ThomGame.Construction.minimalSigmaRecoveredAllPorts_vertex_iff
#print axioms ThomGame.Construction.minimalSigmaRecoveredGraph_sign
#print axioms ThomGame.Pictures.NoncrossingPairing.intervalIndex_strictMono
#print axioms ThomGame.Pictures.NoncrossingPairing.interval_twin
#print axioms ThomGame.Pictures.NoncrossingPairing.interval_noninterlacing
#print axioms ThomGame.Pictures.Pairing.first_twin_pos
#print axioms ThomGame.Pictures.Pairing.firstChord_inside_stable
#print axioms ThomGame.Pictures.Pairing.firstChord_after_stable
#print axioms ThomGame.Pictures.ofFn_firstChord
#print axioms ThomGame.Pictures.Diagram.enclose
#print axioms ThomGame.Pictures.Diagram.labels_enclose
#print axioms ThomGame.Pictures.exists_matching_diagram
#print axioms ThomGame.Pictures.exists_matching_word_diagram
#print axioms ThomGame.Pictures.PortGraph.topOnlyPorts
#print axioms ThomGame.Pictures.PortGraph.topOnlyPairing_twin
#print axioms ThomGame.Pictures.PortGraph.boundaryNext_topOnly
#print axioms ThomGame.Pictures.PortGraph.topOnlyPairing_noninterlacing
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_boundary_only
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_no_hubs
#print axioms ThomGame.Pictures.Diagram.rotatePrefix
#print axioms ThomGame.Pictures.Diagram.labels_rotatePrefix
#print axioms ThomGame.Pictures.Diagram.exposePort
#print axioms ThomGame.Pictures.Diagram.glueFirst
#print axioms ThomGame.Pictures.Diagram.splicePorts
#print axioms ThomGame.Pictures.Diagram.labels_splicePorts
#print axioms ThomGame.Pictures.Diagram.size_splicePorts
#print axioms ThomGame.Pictures.Diagram.sign_splicePorts
#print axioms ThomGame.Pictures.RotationEuler.leftDual_count
#print axioms ThomGame.Pictures.RotationEuler.leftDual_connected
#print axioms ThomGame.Pictures.RotationEuler.cutLoop_product
#print axioms ThomGame.Pictures.RotationEuler.cutLoop_count
#print axioms ThomGame.Pictures.RotationEuler.cutLoop_separates
#print axioms ThomGame.Pictures.FinCircle.hit_before_cut
#print axioms ThomGame.Pictures.FinCircle.splice_sameCycle_of_sbtw
#print axioms ThomGame.Pictures.RotationEuler.circular_noninterlacing
#print axioms ThomGame.Pictures.Pairing.noninterlacing_of_euler
#print axioms ThomGame.Pictures.exists_matching_diagram_of_euler
#print axioms ThomGame.Pictures.RotationEuler.contractEdge_product
#print axioms ThomGame.Pictures.RotationEuler.contractEdge_count
#print axioms ThomGame.Pictures.RotationEuler.contractEdge_connected
#print axioms ThomGame.Pictures.RotationEuler.contractEdge_saturated
#print ThomGame.Pictures.EdgeContraction
#print axioms ThomGame.Pictures.EdgeContraction.involutive
#print axioms ThomGame.Pictures.EdgeContraction.face_eq
#print axioms ThomGame.Pictures.EdgeContraction.edge_eq_or_fixed
#print axioms ThomGame.Pictures.EdgeContraction.preserves_label
#print axioms ThomGame.Pictures.EdgeContraction.connected_iff
#print axioms ThomGame.Pictures.EdgeContraction.count_eq
#print axioms ThomGame.Pictures.EdgeContraction.vertex_count
#print axioms ThomGame.Pictures.EdgeContraction.saturated
#print axioms ThomGame.Pictures.EdgeContraction.terminal_original_connected
#print axioms ThomGame.Pictures.EdgeContraction.terminalComponentEquiv
#print axioms ThomGame.Pictures.EdgeContraction.terminal_length
#print axioms ThomGame.Pictures.EdgeContraction.exists_terminal
#print axioms ThomGame.Pictures.CyclicBlock.formPerm_join
#print axioms ThomGame.Pictures.CyclicBlock.filter_join
#print axioms ThomGame.Pictures.Diagram.joinLabelledBlocks
#print axioms ThomGame.Pictures.Diagram.labels_joinLabelledBlocks
#print ThomGame.Pictures.ResidualMatching.word
#print axioms ThomGame.Pictures.ResidualMatching.pairing
#print axioms ThomGame.Pictures.ResidualMatching.index_strictMono
#print axioms ThomGame.Pictures.ResidualMatching.orderedPairing_twin
#print axioms ThomGame.Pictures.ResidualMatching.orderedPairing_noninterlacing
#print axioms ThomGame.Pictures.ResidualMatching.exists_diagram
#print axioms ThomGame.Pictures.ResidualMatching.exists_diagram_of_euler
#print axioms ThomGame.Pictures.RotationEuler.count_congr
#print axioms ThomGame.Pictures.EdgeContraction.terminalEnumeration
#print axioms ThomGame.Pictures.EdgeContraction.terminalEnumeration_rotation
#print axioms ThomGame.Pictures.EdgeContraction.terminalEdge_step
#print axioms ThomGame.Pictures.EdgeContraction.terminalEdge_involutive
#print axioms ThomGame.Pictures.EdgeContraction.terminalEdge_label
#print axioms ThomGame.Pictures.EdgeContraction.terminalEdge_saturated
#print ThomGame.Pictures.EdgeContraction.residualWord
#print axioms ThomGame.Pictures.EdgeContraction.exists_residual_diagram
#print ThomGame.Pictures.CyclicBlock.IsCycleWord
#print axioms ThomGame.Pictures.CyclicBlock.formPerm_sameCycle
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.mem_iff_sameCycle
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.rotated_of_common
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.join
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.untouched
#print axioms ThomGame.Pictures.CyclicBlock.filter_isRotated
#print axioms ThomGame.Pictures.CyclicBlock.filter_moving_away
#print axioms ThomGame.Pictures.Diagram.exists_cyclic_shift
#print ThomGame.Pictures.DiagramBlock
#print ThomGame.Pictures.RootedBlock
#print axioms ThomGame.Pictures.DiagramBlock.exists_rooted
#print axioms ThomGame.Pictures.DiagramBlock.root_labels
#print axioms ThomGame.Pictures.DiagramBlock.untouched_labels
#print axioms ThomGame.Pictures.RootedBlock.merged_filter
#print axioms ThomGame.Pictures.RootedBlock.merge
#print axioms ThomGame.Pictures.RootedBlock.merge_labels
#print axioms ThomGame.Pictures.BlockIndex.sum_merge
#print ThomGame.Pictures.BlockFamily
#print ThomGame.Pictures.BlockFamily.relations
#print axioms ThomGame.Pictures.BlockFamily.owners_ne
#print axioms ThomGame.Pictures.BlockFamily.mergedBlock_mem
#print axioms ThomGame.Pictures.BlockFamily.mergedBlock_labels
#print axioms ThomGame.Pictures.BlockFamily.merge
#print axioms ThomGame.Pictures.BlockFamily.merge_relations
#print axioms ThomGame.Pictures.EdgeContraction.exists_blockFamily
#print axioms ThomGame.Pictures.BlockFamily.exists_terminal
#print axioms ThomGame.Pictures.CircularPartition.subsetEnumeration_list
#print axioms ThomGame.Pictures.CircularPartition.ofFn_subset_filter
#print axioms ThomGame.Pictures.ResidualMatching.word_transport
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.fullEnumeration_rotation
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.exists_filtered_diagram
#print axioms ThomGame.Pictures.BlockFamily.relations_eq_block
#print axioms ThomGame.Pictures.BlockFamily.exists_closed_diagram
#print axioms ThomGame.Pictures.CyclicBlock.formPerm_ofFn
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.ofFn
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.reverse
#print axioms ThomGame.Pictures.PortGraph.hubPorts_cyclic
#print axioms ThomGame.Pictures.PortGraph.hubPorts_reverse_cyclic
#print axioms ThomGame.Pictures.PortGraph.hubBlock_labels
#print axioms ThomGame.Pictures.PortGraph.hubBlock_mem_owner
#print axioms ThomGame.Pictures.PortGraph.closedBlockFamily
#print axioms ThomGame.Pictures.PortGraph.closedBlockFamily_relations
#check ThomGame.Pictures.PortGraph.exists_closed_diagram_of_rotationEuler
#print axioms ThomGame.Pictures.PortGraph.exists_closed_diagram_of_rotationEuler
#print axioms ThomGame.Pictures.Diagram.labels_traceLeft
#print axioms ThomGame.Pictures.Diagram.labels_traceRight
#print ThomGame.Pictures.Frame.complement
#print axioms ThomGame.Pictures.Frame.labels_fill
#print axioms ThomGame.Pictures.Frame.labels_complement
#print axioms ThomGame.Pictures.Frame.labels_puncture
#print ThomGame.InvolutionPresentation.adjoinRelation
#print axioms ThomGame.Pictures.Diagram.labels_adjoinRelation
#print axioms ThomGame.Pictures.Diagram.exists_erase_absent_relation
#print axioms ThomGame.Pictures.Diagram.exists_frame_of_unique_relation
#check ThomGame.Pictures.Diagram.exists_punctured_diagram
#print axioms ThomGame.Pictures.Diagram.exists_punctured_diagram
#print axioms ThomGame.Pictures.Diagram.exists_punctured_diagram_of_multiset
#print axioms ThomGame.Pictures.RotationEuler.marked_rotation_eq_one
#print axioms ThomGame.Pictures.RotationEuler.count_cap_boundary
#print axioms ThomGame.Pictures.RotationEuler.connected_cap_boundary
#print axioms ThomGame.Pictures.PortGraph.boundaryNext_eq_cyclic
#print ThomGame.Pictures.PortGraph.cappedRotation
#print axioms ThomGame.Pictures.PortGraph.return_eq_cappingReturn_inv
#print axioms ThomGame.Pictures.PortGraph.cappedRotation_count
#print axioms ThomGame.Pictures.PortGraph.cappedRotation_connected
#print axioms ThomGame.Pictures.PortGraph.cappedRotation_saturated
#print axioms ThomGame.Pictures.PortGraph.cappedHubBlock_labels
#print axioms ThomGame.Pictures.PortGraph.topPorts_reverse_cyclic
#print axioms ThomGame.Pictures.PortGraph.outerBlock_labels
#print axioms ThomGame.Pictures.PortGraph.cappedBlockFamily_relations
#check ThomGame.Pictures.PortGraph.exists_diagram_of_rotationEuler_boundary
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_rotationEuler_boundary
#print axioms ThomGame.Pictures.Smoothing.rotationEuler_saturated
#print axioms ThomGame.Pictures.Smoothing.rotation_connected
#print axioms ThomGame.Pictures.Smoothing.hub_relations
#print axioms ThomGame.Pictures.PortGraph.diagram_size_of_hub_labels
#print axioms ThomGame.Pictures.PortGraph.diagram_sign_of_hub_labels
#check ThomGame.Pictures.PortGraph.exists_diagram_of_connected_preserving
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_connected_preserving
#print axioms ThomGame.Pictures.RibbonConnectivity.Connected.lift_restricted
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germInternalPort_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germInternalPort_cut_connected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germCircuitDart_connected
#check ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_connected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_connected
#print ThomGame.Pictures.PortGraph.SimpleCircuit.germSectorExit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germSectorExit_next_marked
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germSectorExit_next_unmarked
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germSectorExit_hit
#check ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_boundaryNext_bottom
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_boundaryNext_bottom
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_boundarySeesComponents
#print axioms ThomGame.Pictures.RotationEuler.deleteEdge_saturated
#print ThomGame.Pictures.RotationEuler.retainEdges
#print axioms ThomGame.Pictures.RotationEuler.retainEdges_involutive
#print axioms ThomGame.Pictures.RotationEuler.retainEdges_saturated
#print axioms ThomGame.Pictures.RotationEuler.count_sum
#print axioms ThomGame.Pictures.RotationEuler.subtype_saturated
#print ThomGame.Pictures.PortGraph.SimpleCircuit.germPartialRotation
#print ThomGame.Pictures.PortGraph.SimpleCircuit.germPartialPairing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germPartial_saturated
#print ThomGame.Pictures.LeafCompletion.pairing
#print axioms ThomGame.Pictures.LeafCompletion.turn_involutive
#print axioms ThomGame.Pictures.LeafCompletion.edge_advances
#print axioms ThomGame.Pictures.LeafCompletion.face_advances
#print axioms ThomGame.Pictures.LeafCompletion.componentEquiv
#print axioms ThomGame.Pictures.LeafCompletion.count_eq
#print axioms ThomGame.Pictures.LeafCompletion.saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germPartialPairing_fixed_iff
#print ThomGame.Pictures.PortGraph.SimpleCircuit.germCompletionPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germCompletionPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germCompletionPorts_pairing
#check ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_rotationEuler
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_rotationEuler
#print ThomGame.Pictures.PortGraph.swapBoundary
#print axioms ThomGame.Pictures.PortGraph.swapBoundary_pairing
#print axioms ThomGame.Pictures.PortGraph.swapBoundary_next
#print axioms ThomGame.Pictures.PortGraph.swapBoundary_rotationEuler
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_forward_bottom
#check ThomGame.Pictures.PortGraph.SimpleCircuit.exists_germ_diagram_preserving
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_germ_diagram_preserving
#check ThomGame.Construction.closedSigmaRimGerm_exists_diagram
#print axioms ThomGame.Construction.closedSigmaRimGerm_exists_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_diagram
#check ThomGame.Construction.closedSigmaRimGerm_minimal_exists_zero_sign_diagram
#print axioms ThomGame.Construction.closedSigmaRimGerm_minimal_exists_zero_sign_diagram
#check ThomGame.Construction.smoothedSigmaRimGerm_minimal_exists_zero_sign_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_minimal_exists_zero_sign_diagram

#check ThomGame.Pictures.CyclicBlock.IsCycleWord.exists_filtered_diagram_of_invariant
#print axioms ThomGame.Pictures.CyclicBlock.IsCycleWord.exists_filtered_diagram_of_invariant
#check ThomGame.Pictures.BlockFamily.exists_closed_diagram_of_saturated
#print axioms ThomGame.Pictures.BlockFamily.exists_closed_diagram_of_saturated
#check ThomGame.Pictures.PortGraph.exists_closed_diagram_of_saturated_preserving
#print axioms ThomGame.Pictures.PortGraph.exists_closed_diagram_of_saturated_preserving

#print ThomGame.Pictures.PortGraph.SimpleCircuit.CappedSide
#print axioms ThomGame.Pictures.RotationEuler.left_dual_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cappedSide_cases
#check ThomGame.Pictures.PortGraph.SimpleCircuit.capped_sector_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.capped_sector_saturated
#print axioms ThomGame.Pictures.CyclicBlock.subtypePorts_filtered_label
#print axioms ThomGame.Pictures.DiagramBlock.restrict_labels
#print axioms ThomGame.Pictures.OrbitEnumeration.retainedList_eq_filter
#check ThomGame.Pictures.PortGraph.SimpleCircuit.sectorPorts_boundary
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sectorPorts_boundary
#check ThomGame.Pictures.PortGraph.SimpleCircuit.sectorBlockFamily_relations
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sectorBlockFamily_relations
set_option pp.explicit true in
#check ThomGame.Pictures.PortGraph.SimpleCircuit.exists_region_diagram_preserving
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_region_diagram_preserving
#check ThomGame.Pictures.PortGraph.SimpleCircuit.germ_region_witnesses_minimal
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_region_witnesses_minimal
#check ThomGame.Pictures.Smoothing.exists_minimal_circuit_diagrams
#print axioms ThomGame.Pictures.Smoothing.exists_minimal_circuit_diagrams
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_frontierWord_in_open
#check ThomGame.Construction.closedSigmaRimRegion_exists_diagram
#print axioms ThomGame.Construction.closedSigmaRimRegion_exists_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimRegion_exists_diagram
#check ThomGame.Construction.smoothedSigmaRimRegion_exists_minimal_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimRegion_exists_minimal_diagram
#print axioms ThomGame.Construction.closedSigmaRimRegion_exists_minimal_diagram
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_minimal_zero_sign_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_minimal_zero_sign_diagram
#print axioms ThomGame.Construction.closedSigmaRimGerm_exists_minimal_zero_sign_diagram
#print axioms ThomGame.Construction.closedSigmaRimFrontierWord_in_neighbourhood
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_retracted_minimal_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_retracted_minimal_diagram
#print axioms ThomGame.Construction.closedSigmaRimGerm_exists_retracted_minimal_diagram

#print ThomGame.Pictures.Diagram.CharacterMinimal
#print axioms ThomGame.Pictures.Diagram.exists_characterMinimal
#print axioms ThomGame.Pictures.Diagram.sun_minimal_iff_characterMinimal
#print axioms ThomGame.Pictures.Diagram.closed_sun_characterMinimal_size_zero
#print axioms ThomGame.Hypergraph.OpenEmbedding.toGeneralizedHom
#print axioms ThomGame.Pictures.embedDiagram_labels_perm
#print axioms ThomGame.Pictures.embedDiagram_size
#print axioms ThomGame.Pictures.embedDiagram_sign_zero
#print axioms ThomGame.Pictures.sunRetraction_boundary_map
#print axioms ThomGame.Pictures.sunRetraction_boundary_spokes
#check ThomGame.Pictures.retractionSunDiagram_minimal
#print axioms ThomGame.Pictures.retractionSunDiagram_minimal
#print axioms ThomGame.Pictures.retractionSunDiagram_retains_labels
#print axioms ThomGame.Construction.sigmaToCycleSun_minimal
#print axioms ThomGame.Construction.closedSigmaRimSunFrontierWord_map
#print axioms ThomGame.Construction.closedSigmaRimSunFrontierWord_length
#print axioms ThomGame.Construction.closedSigmaRimSunFrontierWord_spokes
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_minimal_sun_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_minimal_sun_diagram
#print axioms ThomGame.Construction.closedSigmaRimGerm_exists_minimal_sun_diagram
#print axioms ThomGame.Hypergraph.sunSystem_hypergraph
#print axioms ThomGame.Hypergraph.sunCycle
#print axioms ThomGame.Pictures.sunPresentation_triangular
#print axioms ThomGame.Pictures.PortGraph.sunRimSimpleCircuit_frontier_spokes
#check ThomGame.Pictures.PortGraph.sun_spoke_hub_endpoints
#print axioms ThomGame.Pictures.PortGraph.sun_spoke_hub_endpoints

#print ThomGame.Pictures.PortGraph.SunSpoke
#print ThomGame.Pictures.PortGraph.SunSpoke.switch
#print axioms ThomGame.Pictures.MarkedReturn.pair_return_val
#print axioms ThomGame.Pictures.MarkedReturn.orbitEquivOfHits
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_twin_portSwap
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_character
#check ThomGame.Pictures.PortGraph.SunSpoke.return_congr
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.return_congr
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.faceOrbitEquiv
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_face_card
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_connected
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_circuit_connected
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rotationEuler
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_saturated
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_saturated
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_boundaryNext
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_boundaryNoncrossing
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_boundarySeesComponents
#print ThomGame.Pictures.PortGraph.BoundaryQuadPath
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.boundaryNext
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.first_edge_ne_middle
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.first_edge_ne_last
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.middle_edge_ne_last
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.quad_hubs_away
#check ThomGame.Pictures.PortGraph.SunSpoke.quad_pairs_preserved
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.quad_pairs_preserved
#check ThomGame.Pictures.PortGraph.SunSpoke.switchQuadPath
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switchQuadPath

#check ThomGame.Pictures.RotationEuler.splitVertex_saturated
#print axioms ThomGame.Pictures.RotationEuler.splitVertex_count
#print axioms ThomGame.Pictures.RotationEuler.splitVertex_component_card
#print axioms ThomGame.Pictures.RotationEuler.splitVertex_saturated
#print ThomGame.Pictures.PortGraph.SunSpoke.cancel
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancelPort_left_inv
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancelPort_right_inv
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_twin
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_relations
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_hub_card
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_character
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_sign
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancelFull_rotation
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancelFull_saturated
#check ThomGame.Pictures.PortGraph.SunSpoke.cancel_saturated
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_saturated
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_eulerDefect
#check ThomGame.Pictures.PortGraph.SunSpoke.exists_cancelled_without_junctions
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.exists_cancelled_without_junctions

#print axioms ThomGame.Pictures.PortGraph.cappedJointBlock_labels
#print axioms ThomGame.Pictures.PortGraph.cappedAllBlockFamily_relations
#check ThomGame.Pictures.PortGraph.exists_diagram_of_capped_saturated_preserving
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_capped_saturated_preserving
#print axioms ThomGame.Pictures.PortGraph.adjoin_boundaryNoncrossing
#print axioms ThomGame.Pictures.PortGraph.adjoin_boundarySeesComponents
#print axioms ThomGame.Pictures.PortGraph.boundaryClosure_selectedAccessible
#print axioms ThomGame.Pictures.PortGraph.boundaryClosure_return
#print axioms ThomGame.Pictures.PortGraph.boundaryClosure_rotation
#print axioms ThomGame.Pictures.PortGraph.boundaryClosure_eulerDefect
#check ThomGame.Pictures.PortGraph.cappedRotation_saturated_general
#print axioms ThomGame.Pictures.PortGraph.cappedRotation_saturated_general
#check ThomGame.Pictures.PortGraph.exists_diagram_of_boundary_invariants
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_boundary_invariants
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancelFull_capped_saturated
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cancel_capped_saturated
#check ThomGame.Pictures.PortGraph.SunSpoke.exists_cancelled_diagram
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.exists_cancelled_diagram
#check ThomGame.Pictures.Smoothing.characterMinimal_sun_spoke_same_flip
#print axioms ThomGame.Pictures.Smoothing.characterMinimal_sun_spoke_same_flip
#print axioms ThomGame.Pictures.PortGraph.get_reverseWordIndex
#print axioms ThomGame.Pictures.PortGraph.bottomTop_boundaryNext
#print axioms ThomGame.Pictures.PortGraph.bottomTop_boundaryNoncrossing
#print axioms ThomGame.Pictures.PortGraph.bottomTop_boundarySeesComponents
#print axioms ThomGame.Pictures.PortGraph.bottomTop_eulerDefect
#print axioms ThomGame.Pictures.Diagram.labels_fromReversedTop_perm
#check ThomGame.Pictures.PortGraph.exists_diagram_of_bottom_invariants_preserving
#print axioms ThomGame.Pictures.PortGraph.exists_diagram_of_bottom_invariants_preserving
#check ThomGame.Pictures.PortGraph.SunSpoke.exists_cancelled_bottom_diagram
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.exists_cancelled_bottom_diagram
#check ThomGame.Pictures.Smoothing.characterMinimal_sun_bottom_spoke_same_flip
#print axioms ThomGame.Pictures.Smoothing.characterMinimal_sun_bottom_spoke_same_flip
#print axioms ThomGame.Pictures.Diagram.characterMinimal_sun_bottom_spoke_same_flip
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_oriented_sun_diagram
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_oriented_sun_diagram
#print axioms ThomGame.Construction.closedSigmaRimGerm_exists_oriented_sun_diagram
#print ThomGame.Pictures.PortGraph.SunMinimalState
#print axioms ThomGame.Pictures.Smoothing.sunMinimalState
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.same_flip
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.switch
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.smoothing
#check ThomGame.Pictures.PortGraph.SunMinimalState.exists_minimal_diagram
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.exists_minimal_diagram
#print ThomGame.Pictures.PortGraph.SunSwitchTrace
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.minimalState
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.hub_relations
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.boundaryNext
#check ThomGame.Pictures.PortGraph.SunSwitchTrace.exists_minimal_diagram
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.exists_minimal_diagram
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.quadPath_start
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.quadPath_finish
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.capped_first_step
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.capped_second_step
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.capped_last_step
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.capped_face_word
#check ThomGame.Pictures.PortGraph.BoundaryQuadPath.capped_face_iff
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.capped_face_iff

#print axioms ThomGame.Pictures.PairingCycles.orientationOrbit_component
#check ThomGame.Pictures.PairingCycles.walk_orbit_card
#print axioms ThomGame.Pictures.PairingCycles.walk_orbit_card
#print axioms ThomGame.Pictures.PairingCycles.reverse_vertex_sameCycle
#print axioms ThomGame.Pictures.PairingCycles.switchedWalk_vertex
#print axioms ThomGame.Pictures.PairingCycles.switchedWalk_conjugate
#print axioms ThomGame.Pictures.PairingCycles.switchedWalk_orbit_card_split
#print axioms ThomGame.Pictures.PairingCycles.switchedWalk_orbit_card_join
#print axioms ThomGame.Pictures.PairingCycles.switchedWalk_refines
#print axioms ThomGame.Pictures.PairingCycles.switched_separates
#print axioms ThomGame.Pictures.PairingCycles.switched_joins
#print axioms ThomGame.Pictures.PairingCycles.switchedWalk_away
#print axioms ThomGame.Pictures.PairingCycles.switched_connected_away
#print axioms ThomGame.Pictures.PortGraph.sunRimVertexPairing_port
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.rimSwap_true_val
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rimPairing
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rimVertexPairing
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_rimWalk_conjugate
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rimWalk_conjugate
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sector_of_rotation_port
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_incoming
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_spoke_unmarked
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_spoke_onSide
#check ThomGame.Pictures.PortGraph.SunSpoke.rim_connected_same_orientation
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.rim_connected_same_orientation
#print axioms ThomGame.Pictures.PortGraph.sunRimWalk_orbit_card
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_orbit_card
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.rim_component_card_split
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.rim_component_card_join
#check ThomGame.Pictures.PortGraph.SunMinimalState.rim_component_card_switch
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.rim_component_card_switch
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_separates
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_joins
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_connected_away
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_connected_away
#check ThomGame.Pictures.PortGraph.SunMinimalState.rim_connected_switch_iff
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.rim_connected_switch_iff
#check ThomGame.Pictures.MarkedReturn.connected_return_iff
#print axioms ThomGame.Pictures.MarkedReturn.connected_return_iff
#print axioms ThomGame.Pictures.MarkedReturn.connected_projection_iff
#print axioms ThomGame.Pictures.MarkedReturn.return_component_card
#print axioms ThomGame.Pictures.RotationEuler.restore_deleted_pair
#print axioms ThomGame.Pictures.RotationEuler.restored_connected_return_iff
#check ThomGame.Pictures.PortGraph.SunSpoke.spoke_deleted_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.spoke_deleted_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.spoke_deleted_region_card
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.spoke_restored_pairing
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_spoke_restored_pairing
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.spoke_restored_connected_iff
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_spoke_restored_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_spoke_restored_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutPairing_eq_retainEdges
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.sun_rim_cut_restoration
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.sun_rim_switch_cut_restoration
#check ThomGame.Pictures.PortGraph.SunSpoke.sun_rim_cut_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.sun_rim_cut_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.deleted_hub_connected
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.deleted_patch_connected
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.deleted_connected_locality
#check ThomGame.Pictures.PortGraph.SunSpoke.cut_connected_locality
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.cut_connected_locality
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_marked_iff_connected
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_marked_iff_of_connected
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_onHub_iff_connected
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_marked_away
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_basePort
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_cut_connected_away
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_onSide_away
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_onSide_away
#print axioms ThomGame.Pictures.Pairing.edgePred_edge_iff
#print axioms ThomGame.Pictures.Pairing.edge_subset_card
#check ThomGame.Pictures.PortGraph.sunSideSpokeCount
#print axioms ThomGame.Pictures.PortGraph.sunSideSpoke_twin_iff
#print axioms ThomGame.Pictures.PortGraph.sunSideSpoke_edge_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_spoke_twin_fixed
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_spoke_count_away
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_spoke_count_away
#print axioms ThomGame.Pictures.RibbonConnectivity.rootUnion_conjugate_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_selected_rim_union
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_selected_marked_transport
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_selected_marked_of_same_rim
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_selected_marked_of_same_rim
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_selected_marked_of_join
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_selected_marked_of_join

#print axioms ThomGame.Pictures.RotationEuler.retainEdges_preserves
#print axioms ThomGame.Pictures.RotationEuler.connected_retainEdges
#check ThomGame.Pictures.RotationEuler.connected_retainEdges_iff_of_component
#print axioms ThomGame.Pictures.RotationEuler.connected_retainEdges_iff_of_component
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.opposite_deletion_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.opposite_deletion_onSide_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRimDeletedPairing_eq
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_spoke_onSide_left
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_spoke_onSide_right
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_opposite_spoke_side_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_spoke_side_union
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_spoke_not_opposite
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_connected_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_switchDeleted_refines
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.portSwap_step_spoke_left
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.portSwap_step_spoke_right
#check ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_spoke_separates
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_spoke_separates
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_spoke_regions_disjoint
#check ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_region_card
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_deleted_region_card
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.deleted_spoke_separates
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.deleted_region_card

#print axioms ThomGame.Finite.card_partition_two_singleton
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_onVertex_iff_connected
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_cut_connected_of_rim_away
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_marked_onSide_of_rim_away
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.selectedRimDeletedPairing_left_eq
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.rightRim_marked_on_left_spoke_side
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.selectedRim_opposite_left_side_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.selectedRim_opposite_right_side_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRim_opposite_side_kept
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.rightRim_opposite_side_kept
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.splitLeftRoot_step_base
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.splitRightRoot_step_base
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.leftRimSwitchDeletedPairing_eq_selected
#check ThomGame.Pictures.PortGraph.SunSpoke.split_left_opposite_side_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_left_opposite_side_iff
#check ThomGame.Pictures.PortGraph.SunSpoke.split_right_opposite_side_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_right_opposite_side_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_opposite_sides_disjoint
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_opposite_sides_union
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.not_kept_iff_spoke_edge
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_partition
#check ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_edge_partition
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_edge_partition
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_edges_disjoint
#check ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_spoke_count_lt
#check ThomGame.Pictures.PortGraph.SunMinimalState.split_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.split_spoke_count

#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_twice_flip
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_twice_pairing
#check ThomGame.Pictures.PortGraph.SunSpoke.switch_twice
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_twice
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_twice_onSide
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_twice_sideSpokeCount
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.onSide_union_iff_connected
#print axioms ThomGame.Pictures.PortGraph.sunComponentSpoke_edge_partition
#print axioms ThomGame.Pictures.PortGraph.sunSideSpoke_edges_disjoint
#print axioms ThomGame.Pictures.PortGraph.sunComponentSpokeCount_eq_sides
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_dual_connected
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_component_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_spoke_side_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_spoke_count_add
#check ThomGame.Pictures.PortGraph.SunSpoke.join_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_spoke_count_lt
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.join_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.hasBoundarySide_iff_meetsBoundary
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cut_connected_boundary
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.hasBoundarySide_unique
#check ThomGame.Pictures.PortGraph.SimpleCircuit.boundarySide
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundarySide_spec
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.on_boundarySide_iff_component
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.opposite_boundarySide_has_no_boundary
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_meetsBoundary_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_boundarySide_away
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_boundary_side_witnesses
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_boundarySide_values
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_spoke_side_union
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_old_opposite_sides_disjoint
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_boundary_side_witnesses
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_boundarySide_values
#check ThomGame.Pictures.PortGraph.sunInteriorSpokeCount
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.boundarySide_eq_of_interior_spoke
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_interior_spoke_count_away
#check ThomGame.Pictures.PortGraph.SunSpoke.split_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_interior_spoke_count_lt
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_interior_spoke_count_add
#check ThomGame.Pictures.PortGraph.SunSpoke.join_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_interior_spoke_count_lt
#check ThomGame.Pictures.Diagram.hubsReachBoundary_of_minimum_size
#print axioms ThomGame.Pictures.Diagram.hubsReachBoundary_of_minimum_size
#print axioms ThomGame.Pictures.PortGraph.connected_boundary_of_hubsReachBoundary
#print axioms ThomGame.Pictures.PortGraph.smooth_hubsReachBoundary
#print axioms ThomGame.Pictures.Smoothing.hubsReachBoundary
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.meetsBoundary_of_hubsReachBoundary
#print axioms ThomGame.Pictures.Diagram.sun_hubsReachBoundary
#print axioms ThomGame.Pictures.Smoothing.sun_hubsReachBoundary
#print axioms ThomGame.Pictures.Smoothing.sun_rim_meetsBoundary
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_hubsReachBoundary
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.hubsReachBoundary
#check ThomGame.Pictures.PortGraph.SunSwitchTrace.smoothed_minimal_rims_meetBoundary
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.smoothed_minimal_rims_meetBoundary

#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutPairing_eq_of_marked
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.bases_connected_of_marked
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutInterior_iff_of_marked
#check ThomGame.Pictures.PortGraph.SimpleCircuit.on_opposite_boundarySide_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.on_opposite_boundarySide_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.opposite_boundarySide_iff_of_marked
#check ThomGame.Pictures.PortGraph.sunInteriorSpokeCount_eq_of_connected
#print axioms ThomGame.Pictures.PortGraph.sunInteriorSpokeCount_eq_of_connected
#check ThomGame.Pictures.PortGraph.sunRimInteriorCount
#check ThomGame.Pictures.PortGraph.sunTotalInteriorSpokeCount
#print axioms ThomGame.Pictures.PortGraph.sunRimInteriorCount_component
#print axioms ThomGame.Pictures.PortGraph.sunTotalInteriorSpokeCount_eq_zero_iff
#print axioms ThomGame.Pictures.RibbonConnectivity.away_iff_of_rootUnion
#check ThomGame.Pictures.RibbonConnectivity.unselectedComponentEquiv
#print axioms ThomGame.Pictures.RibbonConnectivity.unselectedComponentEquiv_component
#print axioms ThomGame.Finite.sum_except_two
#print axioms ThomGame.Finite.sum_except_two_of_eq
#print axioms ThomGame.Finite.sum_except_two_of_ne
#check ThomGame.Pictures.PortGraph.SunSpoke.unselectedRimEquiv
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rim_away_iff
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.unselected_rim_interior_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.unselected_rim_interior_sum
#check ThomGame.Pictures.PortGraph.SunSpoke.split_total_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.split_total_interior_spoke_count
#check ThomGame.Pictures.PortGraph.SunSpoke.join_total_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.join_total_interior_spoke_count
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.total_interior_spoke_count_lt
#print axioms ThomGame.Pictures.PortGraph.SunSpoke.switch_rims_meetBoundary
#check ThomGame.Pictures.PortGraph.SunSwitchTrace.Inward
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.rims_meetBoundary
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.switch_interior_measure_lt
#check ThomGame.Pictures.PortGraph.SunMinimalState.exists_no_interior_spoke
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.exists_no_interior_spoke
#check ThomGame.Pictures.PortGraph.SunSwitchTrace.inward_length_bound
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.inward_length_bound
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_hub
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_rim_hub
#print axioms ThomGame.Pictures.Diagram.graph_hub_relations
#check ThomGame.Pictures.Smoothing.exists_terminal_sun_switches
#print axioms ThomGame.Pictures.Smoothing.exists_terminal_sun_switches
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_terminal_sun_graph
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_terminal_sun_graph

#print axioms ThomGame.Pictures.RibbonConnectivity.predicate_of_sameCycle
#print axioms ThomGame.Pictures.RibbonConnectivity.predicate_apply_iff_of_forward
#print axioms ThomGame.Pictures.RibbonConnectivity.Connected.predicate_of_forward
#print axioms ThomGame.Pictures.RibbonConnectivity.Connected.sameCycle_of_fixed_on_component
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cutInterior_iff_of_cut_connected
#check ThomGame.Pictures.PortGraph.SimpleCircuit.marked_of_closed_side
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_of_closed_side
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.onSide_iff_face_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.onSide_iff_port_of_closed
#check ThomGame.Pictures.PortGraph.SimpleCircuit.BoundsFaceOrbit
#check ThomGame.Pictures.PortGraph.SimpleCircuit.faceOrbitEquiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.faceOrbit_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_of_closed_interior
#print axioms ThomGame.Pictures.PortGraph.sunRimCircuit_marked_hub_iff
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_closed_interior
#check ThomGame.Pictures.PortGraph.noInteriorSunSpoke_interior_marked
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_interior_marked
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_interior_iff_face
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_interior_spoke_count
#check ThomGame.Pictures.PortGraph.noInteriorSunSpoke_total_interior_count
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_total_interior_count
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_boundsFaceOrbit
#print axioms ThomGame.Pictures.PortGraph.noInteriorSunSpoke_rims_bound_faces
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.keptDart_isEmpty_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.not_interiorVertex_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.interiorHub_isEmpty_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.interiorJoint_isEmpty_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.keptEdge_isEmpty_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.frontier_isEmpty_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.frontierWord_eq_nil_of_closed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPort_isEmpty_of_closed
#check ThomGame.Pictures.PortGraph.SunFaceState
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.of_terminal
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.interior_marked
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.total_interior_count_eq_zero
#check ThomGame.Pictures.PortGraph.SunFaceState.interior_region_empty
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.interior_region_empty
#check ThomGame.Pictures.Smoothing.exists_sun_face_switches
#print axioms ThomGame.Pictures.Smoothing.exists_sun_face_switches
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_sun_face_graph
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_sun_face_graph

#check ThomGame.Pictures.BlockFamily.replace
#print axioms ThomGame.Pictures.BlockFamily.replace_relations
#print axioms ThomGame.Pictures.BlockFamily.replacement_mem_of_common
#check ThomGame.Pictures.BlockFamily.exists_closed_diagram_cancel_merge
#print axioms ThomGame.Pictures.BlockFamily.exists_closed_diagram_cancel_merge
#print axioms ThomGame.Pictures.triangle_contracted_filter
#check ThomGame.Pictures.triangleCancellationBlock
#print axioms ThomGame.Pictures.triangleCancellationBlock_labels
#print axioms ThomGame.Pictures.Diagram.exists_punctured_after_cancel
#print axioms ThomGame.Pictures.PortGraph.sun_same_hubLabel_port_label
#print axioms ThomGame.Pictures.PortGraph.sun_slotRotation_opposite
#print axioms ThomGame.Pictures.PortGraph.sun_hub_cycleWord
#print axioms ThomGame.Pictures.PortGraph.exists_sun_triangle_cancel_block
#check ThomGame.Pictures.PortGraph.exists_sun_edge_cancelled_top
#print axioms ThomGame.Pictures.PortGraph.exists_sun_edge_cancelled_top
#check ThomGame.Pictures.PortGraph.exists_sun_edge_cancelled_bottom
#print axioms ThomGame.Pictures.PortGraph.exists_sun_edge_cancelled_bottom
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.same_flip_of_same_label_edge
#check ThomGame.Pictures.PortGraph.SimpleCircuit.IsLabelCover
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.side_eq_boundarySide_of_not_interior
#print axioms ThomGame.Pictures.PortGraph.sun_same_label_paired_slot
#print axioms ThomGame.Pictures.PortGraph.sun_same_rim_slot_next
#print axioms ThomGame.Pictures.PortGraph.sunRimDart_exists_hub
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.same_rim_slot_flip_ne
#check ThomGame.Pictures.PortGraph.SunFaceState.rim_edge_labels_ne
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.rim_edge_labels_ne
#check ThomGame.Pictures.PortGraph.SunFaceState.rim_isLabelCover
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.rim_isLabelCover
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.rims_facial_covers
#check ThomGame.Pictures.PortGraph.SunRimsFacialCovers
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.facial_covers
#check ThomGame.Pictures.Smoothing.exists_sun_facial_cover_switches
#print axioms ThomGame.Pictures.Smoothing.exists_sun_facial_cover_switches
#check ThomGame.Construction.smoothedSigmaRimGerm_exists_sun_facial_cover_graph
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_sun_facial_cover_graph

#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.port_not_boundary
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.map
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_map
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_compLeft
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_compRight
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.isLabelCover_compLeft
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.isLabelCover_compRight
#print axioms ThomGame.Pictures.Smoothing.portEmbedding_vertex_iff
#print axioms ThomGame.Pictures.Smoothing.hub_data_of_portEmbedding
#print axioms ThomGame.Pictures.Smoothing.twin_liftTerminal
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reducedCover
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.portEmbedding_reducedCover_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reducedCover_isLabelCover
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_reducedCover
#print axioms ThomGame.Pictures.PortGraph.reduceClosedGluing
#print axioms ThomGame.Pictures.ClosedGluingReduction.leftCircuit_port
#print axioms ThomGame.Pictures.ClosedGluingReduction.rightCircuit_port
#print axioms ThomGame.Pictures.ClosedGluingReduction.leftCircuit_boundsFaceOrbit
#print axioms ThomGame.Pictures.ClosedGluingReduction.rightCircuit_boundsFaceOrbit
#print axioms ThomGame.Pictures.ClosedGluingReduction.hub_relations
#print axioms ThomGame.Pictures.ClosedGluingReduction.euler
#print axioms ThomGame.Pictures.ClosedGluingReduction.exists_diagram
#check ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_reducedCover
#check ThomGame.Pictures.ClosedGluingReduction.leftCircuit_boundsFaceOrbit
#check ThomGame.Pictures.ClosedGluingReduction.exists_diagram

#print axioms ThomGame.exists_triangleFlip
#print axioms ThomGame.triangleFlip_turn
#print axioms ThomGame.Hypergraph.OpenEmbedding.slotEquiv_label
#print axioms ThomGame.Hypergraph.OpenEmbedding.slotEquiv_turn
#print axioms ThomGame.Pictures.PortGraph.embedRows
#print axioms ThomGame.Pictures.PortGraph.rowEmbeddingPorts_twin
#print axioms ThomGame.Pictures.PortGraph.rowEmbeddingPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.embedRows_hub_relations
#print axioms ThomGame.Pictures.PortGraph.embedRows_boundaryNoncrossing
#print axioms ThomGame.Pictures.PortGraph.embedRows_boundarySeesComponents
#print axioms ThomGame.Pictures.PortGraph.embedRows_eulerDefect
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.embedRowsCircuit_boundsFaceOrbit
#print axioms ThomGame.Pictures.OrbitEnumeration.length_congr
#print axioms ThomGame.Pictures.OrbitEnumeration.dart_congr
#print axioms ThomGame.Pictures.PortGraph.embeddedRimEquiv_walk
#print axioms ThomGame.Pictures.PortGraph.embeddedRim_port
#print axioms ThomGame.Pictures.PortGraph.embeddedRim_boundsFaceOrbit
#print axioms ThomGame.Pictures.PortGraph.embeddedRim_isLabelCover
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.embedRows
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.embedRows_darts
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.embedRows_capped_face
#print axioms ThomGame.Construction.numberedWheelSunEmbedding_rhs_zero
#print axioms ThomGame.Construction.numberedWheelSunEmbedding_rim
#print axioms ThomGame.Construction.includeWheelSunGraph
#print axioms ThomGame.Construction.includeWheelSunPorts_twin
#print axioms ThomGame.Construction.includeWheelSunPorts_rotation
#print axioms ThomGame.Construction.includedWheelSunRims_facial_covers
#print axioms ThomGame.Construction.includeWheelSunAtFrontier
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_included_sun
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_region_hub_card_of_connected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germ_region_sign_of_connected
#print axioms ThomGame.Construction.IncludedWheelSun.gluedRimCircuit_port
#print axioms ThomGame.Construction.IncludedWheelSun.gluedRimCircuit_facial_cover
#print axioms ThomGame.Construction.IncludedWheelSun.glue_hub_relations
#print axioms ThomGame.Construction.includedSunGluing_hub_card
#print axioms ThomGame.Construction.includedSunGluing_sign
#print axioms ThomGame.Construction.includedSunGluing_exists_minimal_diagram
#print axioms ThomGame.Construction.smoothedSigmaRim_exists_normalized_gluing
#check ThomGame.Construction.includeWheelSunAtFrontier
#check ThomGame.Construction.smoothedSigmaRim_exists_normalized_gluing

#print axioms ThomGame.Pictures.RotationEuler.retainRotation_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionFullRotation_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_rotationEuler
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_eulerDefect
#print axioms ThomGame.Pictures.MarkedReturn.perm_split_unmarked
#print axioms ThomGame.Pictures.RotationEuler.eraseSlots_saturated
#print axioms ThomGame.Pictures.RotationEuler.firstReturnRotation_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionCappedRotation_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionCappedPorts_pairing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionCappedPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionGraph_swapBoundary_capped_saturated
#print axioms ThomGame.Pictures.RotationEuler.joinVertex_count
#print axioms ThomGame.Pictures.RotationEuler.joinVertex_component_card
#print axioms ThomGame.Pictures.RotationEuler.joinVertex_saturated
#print axioms ThomGame.Pictures.PortGraph.capSeamRotation_step
#print axioms ThomGame.Pictures.PortGraph.capSeamRotation_sameCycle
#print axioms ThomGame.Pictures.PortGraph.capSeamRotation_saturated
#print axioms ThomGame.Pictures.PortGraph.capSeamRotation_all
#print axioms ThomGame.Pictures.PortGraph.comp_saturated_of_capped
#print axioms ThomGame.Pictures.PortGraph.cappedRotation_saturated_of_boundary_invariants
#print axioms ThomGame.Pictures.ClosedGluingReduction.saturated_of_capped
#print axioms ThomGame.Pictures.ClosedGluingReduction.exists_diagram_of_capped
#print axioms ThomGame.Pictures.PortGraph.castPorts_pairing
#print axioms ThomGame.Pictures.PortGraph.castPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.castBoundary_isLabelCover
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.bottomTopCircuit_boundsFaceOrbit
#print axioms ThomGame.Pictures.Diagram.labels_reverseBottom_perm
#print axioms ThomGame.Pictures.Diagram.Minimal.reverseBottom
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_reversed_included_sun
#print axioms ThomGame.Construction.IncludedWheelSun.topPorts_bottom
#print axioms ThomGame.Construction.IncludedWheelSun.topPorts_pairing
#print axioms ThomGame.Construction.IncludedWheelSun.topPorts_rotation
#print axioms ThomGame.Construction.IncludedWheelSun.topGraph_capped_saturated
#print axioms ThomGame.Construction.IncludedWheelSun.orientedRimCircuit_port
#print axioms ThomGame.Construction.IncludedWheelSun.orientedRimCircuit_facial_cover
#print axioms ThomGame.Construction.IncludedWheelSun.orientedGlue_hub_relations
#print axioms ThomGame.Construction.includedSunOrientedGluing_euler
#print axioms ThomGame.Construction.includedSunOrientedGluing_hub_card
#print axioms ThomGame.Construction.includedSunOrientedGluing_sign
#print axioms ThomGame.Construction.includedSunOrientedGluing_exists_minimal_diagram
#print axioms ThomGame.Construction.smoothedSigmaRim_exists_oriented_normalized_gluing

-- Retraction and normalization on the actual germ, retaining its quadrilaterals.
#print axioms ThomGame.Hypergraph.GeneralizedHom.retained_incident_image
#print axioms ThomGame.Hypergraph.GeneralizedHom.retained_map_incidence
#print axioms ThomGame.SparseSystem.mappedColumnSlot_surjective
#print axioms ThomGame.SparseSystem.mappedSlotEquiv_label
#print axioms ThomGame.SparseSystem.mappedSlotEquiv_turn
#print axioms ThomGame.Pictures.PortGraph.RowRelabelling.ports_twin
#print axioms ThomGame.Pictures.PortGraph.RowRelabelling.ports_rotation
#print axioms ThomGame.Pictures.PortGraph.RowRelabelling.eulerDefect
#print axioms ThomGame.Pictures.PortGraph.RowRelabelling.quadPath_capped_face
#print axioms ThomGame.Pictures.filterMap_card_retained
#print axioms ThomGame.Pictures.PortGraph.hubs_retained_of_filterMap_card
#print axioms ThomGame.Pictures.PortGraph.RowRelabelling.ofRetained_hub_relations
#print axioms ThomGame.Pictures.PortGraph.RowRelabelling.ofRetained_port_image
#print axioms ThomGame.Pictures.PortGraph.topBottom_pairing
#print axioms ThomGame.Pictures.PortGraph.topBottom_boundaryNoncrossing
#print axioms ThomGame.Pictures.PortGraph.topBottom_eulerDefect
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.topBottom_firstDart
#print axioms ThomGame.Pictures.PortGraph.forwardBottom_swapBoundary_noncrossing
#print axioms ThomGame.Pictures.PortGraph.forwardBottom_swapBoundary_sees
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.hubsReachBoundary_of_connected
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.exists_facial_cover_switches_of_connected
#print axioms ThomGame.Construction.germSunInitialPorts_twin
#print axioms ThomGame.Construction.germSunInitialPorts_rotation
#print axioms ThomGame.Construction.germSunInitialGraph_minimal
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_structural_sun
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.ports_label
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.ports_vertex_iff
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.ports_boundaryDart
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.quadPath_firstDart
#print axioms ThomGame.Pictures.PortGraph.SunSwitchTrace.quad_pairs_preserved
#print axioms ThomGame.Construction.germSunNormalizedQuad_pairs
#print axioms ThomGame.Construction.smoothedSigmaRimGerm_exists_structural_normalization
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_swapBoundary_twin_top_onCircuit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germQuad_firstHub_onCircuit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germQuad_secondHub_onCircuit
#print axioms ThomGame.Pictures.PortGraph.rimGermQuad_labels_in_open
#print axioms ThomGame.Construction.smoothedSigmaRimGermQuad_labels_in_neighbourhood
#print axioms ThomGame.Construction.germSunNormalizedQuad_labels
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.castBoundary_firstDart
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.bottomTop_firstDart
#print axioms ThomGame.Construction.germSunTopPorts_top
#print axioms ThomGame.Construction.germSunTopQuad_start
#print axioms ThomGame.Construction.germSunTopQuad_finish
#print axioms ThomGame.Construction.germSunTopQuad_pairs
#print axioms ThomGame.Construction.germSunTopQuad_labels
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.start
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.finish
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.circuitStep
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.labels_twin
#print axioms ThomGame.Construction.germSunQuadReplacement
#print axioms ThomGame.Construction.smoothedSigmaRim_exists_structural_oriented_gluing
#check ThomGame.Pictures.RotationEuler.firstReturnRotation_saturated
#check ThomGame.Pictures.PortGraph.comp_saturated_of_capped
#check ThomGame.Construction.smoothedSigmaRim_exists_oriented_normalized_gluing
#check ThomGame.Construction.germSunQuadReplacement
#check ThomGame.Construction.smoothedSigmaRim_exists_structural_oriented_gluing

-- Whole crossing faces, joint suppression, and actual germ quadrilateral support.
#print axioms ThomGame.Pictures.PortGraph.vertex_iff_of_rotation_equiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.pairs_of_side
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.mapAlong_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_mapAlong
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.gluedPorts_vertices
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.seamSwap_map
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.gluedPorts_left_step
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.gluedPorts_right_step
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.crossingCircuit_face
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.crossingCircuit_face_label
#print axioms ThomGame.Pictures.PortGraph.facialCircuitOfOrbit_face
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reduced_face_vertices
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reducedFacialCircuit_face
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reducedFacialCircuit_dart_original
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reducedFacialCircuit_complete
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_terminal_of_quad_crossing
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.gluedPorts_terminal_iff
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.reducedCrossingCircuit_face
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.reducedCrossingCircuit_label
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.reducedCrossingCircuit_complete
#print axioms ThomGame.Construction.germSunTopPorts_vertices
#print axioms ThomGame.Construction.germSun_crossing_face_survives
#print axioms ThomGame.Hypergraph.Cycle.row_nonrim_unique
#print axioms ThomGame.Pictures.PortGraph.row_label_injective_at_vertex
#print axioms ThomGame.Pictures.PortGraph.row_rotation_ne_self
#print axioms ThomGame.Pictures.PortGraph.row_twin_vertex_ne
#print axioms ThomGame.Pictures.PortGraph.continuing_common_edge_leaves_first
#print axioms ThomGame.Pictures.PortGraph.frontier_rotation_marked
#print axioms ThomGame.Pictures.PortGraph.frontier_common_edge_exits
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadPath.ofThreeSteps
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germGraph_three_steps
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germTopInternalPort_step
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germTop_quad_of_crossing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germVertex_exterior_onCircuit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germFaceSource_label
#print axioms ThomGame.Pictures.PortGraph.rimFace_entry_quad
#print axioms ThomGame.Pictures.PortGraph.rimFace_marked_quad
#print axioms ThomGame.Pictures.PortGraph.rimFace_germ_internal_supported
#print axioms ThomGame.Pictures.PortGraph.rimFace_germ_supported
#print axioms ThomGame.Pictures.PortGraph.rimFace_germ_supported_of_entry
#check ThomGame.Construction.germSun_crossing_face_survives
#check ThomGame.Pictures.PortGraph.rimFace_germ_supported_of_entry

-- Original faces lifted through the actual subdivision and preserved by one normalization.
#print axioms ThomGame.Hypergraph.Cycle.empty_boundary_no_rim
#print axioms ThomGame.Pictures.PortGraph.reverseCompPorts_pairing
#print axioms ThomGame.Pictures.PortGraph.reverseCompPorts_rotation
#print axioms ThomGame.Pictures.PortGraph.reverseCompPorts_step
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reverseComposition_face
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedFaceProjection_pairing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedFaceProjection_step
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedFaceProjection_germ
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.face_vertex_injective
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.face_excludes_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedFace_vertex_injective
#print axioms ThomGame.Pictures.Smoothing.circuitEmbedding_surjective
#print axioms ThomGame.Pictures.Smoothing.every_circuit_meets_image
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.gluedFaceProjection_sameCycle_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftPort_projection
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftPort_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.liftedGermCircuit_range
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftedCircuit_face
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftedCircuit_complete
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftedCircuit_terminal_original
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftedCircuit_range
#print axioms ThomGame.Pictures.PortGraph.orientedLiftedRimCircuit_supported
#print axioms ThomGame.Pictures.PortGraph.orientedLiftedRimCircuit_crosses
#print axioms ThomGame.Construction.numberedWheelCycles_intersection_unique
#print axioms ThomGame.Construction.liftedSigmaRimCircuit_supported
#print axioms ThomGame.Pictures.PortGraph.rimFace_replacement_survives
#print axioms ThomGame.Pictures.PortGraph.rimFace_replacement_survives_equiv
#print axioms ThomGame.Construction.germSun_original_crossing_face_survives
#print axioms ThomGame.Construction.germSun_preserves_original_crossing_faces
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.liftedFace_replacement_survives
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.liftedFace_replacement_survives_equiv
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.germFaceSource_meets_germ
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exteriorFace_not_germ_source
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exteriorLiftedCircuit_avoids_germ
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exteriorLiftedCircuit_supported
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exteriorFace_replacement_survives
#print axioms ThomGame.Construction.germSun_preserves_exterior_faces
#print axioms ThomGame.Construction.smoothedSigmaRim_exists_face_preserving_normalization
#check ThomGame.Pictures.PortGraph.rimFace_replacement_survives_equiv
#check ThomGame.Construction.GermSunPreservesOriginalCrossingFaces
#check ThomGame.Construction.GermSunPreservesExteriorFaces
#check ThomGame.Construction.smoothedSigmaRim_exists_face_preserving_normalization

-- Actual alternating circuit, spoke matching, remaining ports and erasure accounting.
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_hub_ports
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.hubAt_injective
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.hubAtRangeEquiv
#print axioms ThomGame.Pictures.PortGraph.sunBand_pair_slots
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_vertex_ports
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_spoke_partner
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandPartner_paired
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandPartner_involutive
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandPartner_ne_self
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandPartner_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_length_even
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandExternalPort_unmarked
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandExternalPort_partner_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandExternalPort_unique
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandExternalPort_complete
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.erasedCircuitHub_sum
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.erasedCircuitHub_card_lt
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_sum_weight_zero
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_erased_weight
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_label_count_even
#check ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandExternalPort_complete
#check ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_erased_weight

-- Actual cut graphs, capped Euler preservation, and Slofstra Lemma 10.6.
#print axioms ThomGame.Pictures.Pairing.orderedPorts
#print axioms ThomGame.Pictures.Pairing.card_ordered_edges
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandErasurePorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandErasureGraph_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandErasureGraph_character
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandErasureGraph_exists_smoothed
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutKeep_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutLabel_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutKeep_hubAt_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutPorts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutPort_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutGraph_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutGraph_character
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutGraph_hub_card_lt
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutReturn_joint
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutGraph_cappedRotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBandCutGraph_capped_saturated
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_sunBand_erased_top_diagram
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_sunBand_erased_bottom_diagram
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.no_sunBand_circuit
#print axioms ThomGame.Pictures.PortGraph.SunMinimalState.circuit_has_label_outside_sunBand
#print axioms ThomGame.Pictures.PortGraph.SunFaceState.no_sunBand_circuit
#print axioms ThomGame.Pictures.Smoothing.no_sunBand_circuit
#print axioms ThomGame.Construction.IncludedWheelSun.pullbackCircuit_label
#print axioms ThomGame.Construction.IncludedWheelSun.no_numberedBand_circuit_of_faceState
#check ThomGame.Pictures.PortGraph.SimpleCircuit.exists_sunBand_erased_bottom_diagram
#check ThomGame.Pictures.PortGraph.SunMinimalState.no_sunBand_circuit
#check ThomGame.Construction.IncludedWheelSun.no_numberedBand_circuit_of_faceState
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.sunBand_of_single_rim_label
#print axioms ThomGame.Pictures.PortGraph.NoSunBandCircuit.no_single_rim_label
#print axioms ThomGame.Construction.IncludedWheelSun.no_other_wheel_circuit
#print axioms ThomGame.Construction.IncludedWheelSun.circuit_has_label_outside_other_wheel
#check ThomGame.Construction.IncludedWheelSun.no_other_wheel_circuit

-- Arbitrary reduced-cycle classification and unique facial rim components.
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.pullback
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.pullback_port
#print axioms ThomGame.Pictures.Smoothing.portEmbedding_twin_of_terminal
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverUnsubdivided_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverUnsubdivided_terminal
#print axioms ThomGame.Pictures.PortGraph.compSide_twin
#print axioms ThomGame.Pictures.PortGraph.compSide_of_terminal_vertex
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.lies_in_one_input
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_input_circuit
#print axioms ThomGame.Pictures.ClosedGluingReduction.input_preimage_of_no_removed_joint
#print axioms ThomGame.Pictures.ClosedGluingReduction.classify_circuit
#print axioms ThomGame.Construction.IncludedWheelSun.fromTopCircuit_port
#print axioms ThomGame.Construction.IncludedWheelSun.no_other_top_circuit
#print axioms ThomGame.Construction.IncludedWheelSun.oriented_other_circuit_seam_or_exterior
#print axioms ThomGame.Construction.IncludedWheelSun.oriented_primary_circuit_input_preimage
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.length_eq_of_marked_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_face_of_marked_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_of_rim_at_vertex
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_iff_rimComponent
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_iff_of_common_rim_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_iff_of_common_rim_edge
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_face_of_common_rim_port
#print axioms ThomGame.Construction.IncludedWheelSun.orientedRimCircuit_rim
#print axioms ThomGame.Construction.IncludedWheelSun.oriented_primary_face_of_right_dart
#print axioms ThomGame.Construction.IncludedWheelSun.oriented_primary_facial_or_exterior
#print axioms ThomGame.Construction.IncludedWheelSun.oriented_primary_nonfacial_exterior
#print axioms ThomGame.Construction.includedSunOrientedGluing_primary_facial_or_exterior
#check ThomGame.Pictures.ClosedGluingReduction.classify_circuit
#check ThomGame.Construction.IncludedWheelSun.oriented_other_circuit_seam_or_exterior
#check ThomGame.Construction.includedSunOrientedGluing_primary_facial_or_exterior

-- Recover actual complementary-region circuits in the original closed graph.
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_iff_image_orbit
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.mapInterior
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.mapInterior_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.unswapBoundary_face_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPortEmbedding_vertex
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.regionPortEmbedding_step
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverRegionCircuit_not_germ
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverRegionCircuit_face_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverSwappedRegionCircuit_port
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverSwappedRegionCircuit_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoverSwappedRegionCircuit_face_iff
#print axioms ThomGame.Pictures.ClosedGluingReduction.boundsFaceOrbit_of_leftPreimage
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.recoveredExteriorPreimage_nonfacial
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_original_of_exterior_preimage
#print axioms ThomGame.Construction.sigma_labelled_circuit_facial_of_rims
#print axioms ThomGame.Construction.includedSunOrientedGluing_exterior_original
#print axioms ThomGame.Construction.includedSunOrientedGluing_exterior_facial
#print axioms ThomGame.Construction.includedSunOrientedGluing_primary_nonfacial_original
#print axioms ThomGame.Construction.includedSunOrientedGluing_other_nonfacial_meets_seam
#check ThomGame.Construction.includedSunOrientedGluing_primary_nonfacial_original
#check ThomGame.Construction.includedSunOrientedGluing_other_nonfacial_meets_seam

-- Actual seam faces and strict descent on nonfacial component quotients.
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_iff_face_or_twin
#print axioms ThomGame.Pictures.Smoothing.sameCycle_twin_portEmbedding
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.reducedFacialCircuit_marked_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedFaceProjection_pairing
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.orientedLiftedCircuit_marked_seam
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.face_exterior_of_frontier_edge
#print axioms ThomGame.Pictures.PortGraph.orientedLiftedRimCircuit_supported_of_side
#print axioms ThomGame.Pictures.PortGraph.BoundaryQuadReplacement.reducedCrossingCircuit_marked_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.liftedFace_replacement_meets_seam
#print axioms ThomGame.Pictures.PortGraph.rim_circuit_facial_of_meets_seam
#print axioms ThomGame.Construction.germSun_seam_circuit_facial
#print axioms ThomGame.Construction.germSun_other_circuit_facial
#print axioms ThomGame.Construction.germSun_other_rims_facial
#print axioms ThomGame.Pictures.PortGraph.rimComponentFacial_iff_circuit
#print axioms ThomGame.Pictures.PortGraph.nonfacialRimCircuit_marked
#print axioms ThomGame.Pictures.PortGraph.nonfacialRimCircuit_not_face
#print axioms ThomGame.Pictures.PortGraph.nonfacialRimComponent_ext
#print axioms ThomGame.Pictures.PortGraph.nonfacialRimCount_eq_zero_iff
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.marked_iff_of_recovered_exterior
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.nonfacialRimCount_lt_of_exterior_preimages
#print axioms ThomGame.Construction.sigmaNonfacialRimCount_eq_zero_iff
#print axioms ThomGame.Construction.includedSunOrientedGluing_nonfacial_count_lt
#print axioms ThomGame.Construction.smoothedSigmaRim_exists_decreasing_replacement
#check ThomGame.Pictures.PortGraph.rim_circuit_facial_of_meets_seam
#check ThomGame.Pictures.PortGraph.SimpleCircuit.nonfacialRimCount_lt_of_exterior_preimages
#check ThomGame.Construction.germSun_other_rims_facial
#check ThomGame.Construction.smoothedSigmaRim_exists_decreasing_replacement

-- Actual graph states: component extraction proves connectivity from minimality.
#print axioms ThomGame.Pictures.PortGraph.Selection.selectedPorts
#print axioms ThomGame.Pictures.PortGraph.Selection.graph_rotation
#print axioms ThomGame.Pictures.PortGraph.Selection.graph_pairing
#print axioms ThomGame.Pictures.PortGraph.Selection.graph_saturated
#print axioms ThomGame.Pictures.PortGraph.Selection.exists_closed_diagram
#print axioms ThomGame.Pictures.PortGraph.exists_component_diagram
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.of_witness
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.exists_minimal_diagram
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.hubs_in_odd_component
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.hubs_reachable
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.vertices_reachable
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.exists_minimal_circuit_diagrams
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.exists_minimal_zero_sign_germ
#print axioms ThomGame.Pictures.Smoothing.closedMinimalOddState
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.exists_minimal_stellar_rim_germ
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_state
#print axioms ThomGame.Construction.SigmaMinimalState.exists_minimal_stellar_germ
#print axioms ThomGame.Construction.SigmaMinimalState.exists_minimal_stellar_sun
#print axioms ThomGame.Construction.smoothedSigmaRim_exists_decreasing_state
#check ThomGame.Pictures.PortGraph.ClosedMinimalOddState
#check ThomGame.Pictures.PortGraph.ClosedMinimalOddState.hubs_reachable
#check ThomGame.Pictures.PortGraph.ClosedMinimalOddState.exists_minimal_circuit_diagrams
#check ThomGame.Construction.J_sigma_eq_one_iff_closed_minimal_state
#check ThomGame.Construction.SigmaMinimalState.exists_minimal_stellar_sun
#check ThomGame.Construction.smoothedSigmaRim_exists_decreasing_state

-- Iterate on the actual output graph, using only size/sign/Euler diagram witnesses.
#check ThomGame.Construction.SigmaGraphWitness
#print ThomGame.Construction.SigmaGraphWitness
#print axioms ThomGame.Construction.SigmaGraphWitness.ofSmoothing
#print axioms ThomGame.Construction.SigmaGraphWitness.minimalState
#print axioms ThomGame.Construction.SigmaGraphWitness.minimal_odd_stellar_rim_hasZeroSignGerm
#print axioms ThomGame.Construction.SigmaMinimalState.exists_graph_witness
#print axioms ThomGame.Construction.SigmaMinimalState.exists_decreasing_replacement
#print axioms ThomGame.Construction.SigmaMinimalState.exists_facial_replacement
#print axioms ThomGame.Construction.SigmaMinimalState.exists_facial_on
#print axioms ThomGame.Construction.SigmaMinimalState.exists_stellar_normalization
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_stellar_normalized_state
#check ThomGame.Construction.SigmaMinimalState.exists_graph_witness
#check ThomGame.Construction.SigmaMinimalState.exists_decreasing_replacement
#check ThomGame.Construction.SigmaMinimalState.exists_facial_replacement
#check ThomGame.Construction.SigmaMinimalState.exists_facial_on
#check ThomGame.Construction.SigmaMinimalState.exists_stellar_normalization
#check ThomGame.Construction.J_sigma_eq_one_iff_stellar_normalized_state

-- Genuine two-hub cancellation proves facial label covers on the actual graph.
#print axioms ThomGame.Pictures.PortGraph.row_hub_cycleWord
#print axioms ThomGame.Pictures.PortGraph.exists_row_triangle_cancel_block
#print axioms ThomGame.Pictures.PortGraph.exists_row_edge_cancelled
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.row_same_flip_of_same_label_edge
#print axioms ThomGame.Pictures.PortGraph.row_same_label_paired_slot
#print axioms ThomGame.Pictures.PortGraph.rim_facial_port_flip_ne
#print axioms ThomGame.Pictures.PortGraph.ClosedMinimalOddState.rim_isLabelCover_of_facial
#print axioms ThomGame.Construction.SigmaMinimalState.facial_covers_of_facial
#print axioms ThomGame.Construction.SigmaMinimalState.exists_stellar_facial_covers
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_stellar_facial_covers
#check ThomGame.Pictures.PortGraph.exists_row_edge_cancelled
#check ThomGame.Pictures.PortGraph.ClosedMinimalOddState.rim_isLabelCover_of_facial
#print ThomGame.Construction.SigmaRimsFacialCovers
#check ThomGame.Construction.SigmaMinimalState.exists_stellar_facial_covers
#check ThomGame.Construction.J_sigma_eq_one_iff_stellar_facial_covers

-- Covered subpaths: actual endpoints, cut sides, and complete path-copy components.
#print ThomGame.Pictures.PortGraph.EdgeHasDistinctHubLabels
#print ThomGame.Pictures.PortGraph.SimpleCircuit.RestrictedAdj
#print ThomGame.Pictures.PortGraph.SimpleCircuit.RestrictedConnected
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.isLabelCover_iff_marked_edges
#print axioms ThomGame.Pictures.PortGraph.rim_cover_edge
#print axioms ThomGame.Pictures.PortGraph.rim_unmarked_same_vertex_eq
#print axioms ThomGame.Pictures.PortGraph.rim_face_shared_edge_frontiers
#print axioms ThomGame.Pictures.PortGraph.rim_shared_face_frontier_iff
#print axioms ThomGame.Pictures.PortGraph.covered_rim_connected_frontier_iff
#print axioms ThomGame.Pictures.PortGraph.covered_rim_component_common_side
#print axioms ThomGame.Pictures.PortGraph.covered_rim_edges_have_distinct_labels
#print axioms ThomGame.Construction.numbered_oddWheelCycle_covered
#print axioms ThomGame.Construction.odd_covered_edge_distinct_labels
#print axioms ThomGame.Construction.odd_covered_component_common_side
#print axioms ThomGame.Construction.odd_covered_component_onSide
#print axioms ThomGame.Pictures.PortGraph.exists_paired_rowLabelPort
#print axioms ThomGame.Pictures.PortGraph.rowEdgeHubEquiv
#print axioms ThomGame.Pictures.PortGraph.rowEdgeHubEquiv_pairing
#print axioms ThomGame.Pictures.PortGraph.cycleEdgeHubEquiv_eq_iff
#print ThomGame.Pictures.PortGraph.RowPath
#print ThomGame.Pictures.PortGraph.RowPath.Adj
#print ThomGame.Pictures.PortGraph.RowPath.Connected
#print axioms ThomGame.Pictures.PortGraph.RowPath.ofCycleSegment
#print axioms ThomGame.Pictures.PortGraph.RowPath.hubEquiv
#print axioms ThomGame.Pictures.PortGraph.RowPath.lift_edge_unique
#print axioms ThomGame.Pictures.PortGraph.RowPath.adj_lift_iff
#print axioms ThomGame.Pictures.PortGraph.RowPath.connected_iff_seed
#print axioms ThomGame.Pictures.PortGraph.RowPath.componentEquiv
#print axioms ThomGame.Pictures.PortGraph.RowPath.component_card
#print axioms ThomGame.Construction.oddCoveredRowPath_edges
#print axioms ThomGame.Construction.oddPathHubEquiv
#print axioms ThomGame.Construction.oddPath_connected_iff
#print axioms ThomGame.Construction.oddPath_component_card
#print axioms ThomGame.Construction.oddPath_hubs_on_rim
#print axioms ThomGame.Construction.oddPath_connected_in_rim
#print axioms ThomGame.Construction.oddPath_common_side
#check ThomGame.Pictures.PortGraph.covered_rim_component_common_side
#check ThomGame.Pictures.PortGraph.RowPath.adj_lift_iff
#check ThomGame.Pictures.PortGraph.RowPath.componentEquiv
#check ThomGame.Construction.oddPathHubEquiv
#check ThomGame.Construction.oddPath_connected_iff
#check ThomGame.Construction.oddPath_component_card
#check ThomGame.Construction.oddPath_common_side

-- Actual two-edge insertion: no planarity or minimality conclusions are fields.
#print ThomGame.Pictures.PortGraph.RowPairInsertion
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.ports
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.twin_first
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.twin_second
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.twin_partner_first
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.twin_partner_second
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.twin_spoke
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.twin_old_away
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.graph_relations
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.graph_hub_card
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.graph_character
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.graph_sign
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.graph_opposite_flips
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.rotation_old
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.oldCircuit_face
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.oldCircuit_cover
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.rimEquiv
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.rimEquiv_walk
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.rim_length
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.rim_port
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.all_rims_facial_covers
#print axioms ThomGame.Construction.odd_row_columns_not_other_cycle
#print axioms ThomGame.Construction.odd_row_spoke_not_cycle
#print axioms ThomGame.Construction.oddPathInsertion
#print axioms ThomGame.Construction.oddPathInsertion_first_vertex
#print axioms ThomGame.Construction.oddPathInsertion_second_vertex
#print axioms ThomGame.Construction.oddPathInsertedGraph_hub_card
#print axioms ThomGame.Construction.oddPathInsertedGraph_character
#print axioms ThomGame.Construction.oddPathInsertedGraph_sign
#print axioms ThomGame.Construction.oddPathInsertedGraph_stellar_facial_covers
#check ThomGame.Pictures.PortGraph.RowPairInsertion.graph
#check ThomGame.Pictures.PortGraph.RowPairInsertion.graph_relations
#check ThomGame.Pictures.PortGraph.RowPairInsertion.all_rims_facial_covers
#check ThomGame.Construction.oddPathInsertion
#check ThomGame.Construction.oddPathInsertedGraph_character
#check ThomGame.Construction.oddPathInsertedGraph_stellar_facial_covers

-- Genuine face returns, Euler preservation, and the actual new facial pentagon.
#print ThomGame.Pictures.PortGraph.SimpleCircuit.MarkedPath
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.return_hit
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.return_congr
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.all_faces_hit_old
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.faceOrbitEquiv
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.face_count_of_same_face
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.old_edge_path
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.componentMap_surjective
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.component_card_le
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.vertex_card
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.edge_card
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.eulerCount_preserved
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.eulerDefect_eq_zero
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.component_card_eq_of_same_face
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.empty_corner_rotation
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.empty_corner_rotation_of_sector
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.empty_corner_sameCycle
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.MarkedPath.exists_face_orientation_and_corners
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.boundsFaceOrbit_of_corner_rotation
#print axioms ThomGame.Pictures.PortGraph.RowPath.markedPath
#print axioms ThomGame.Pictures.PortGraph.RowPath.exists_face_orientation
#print axioms ThomGame.Construction.oddPathInsertion_exists_same_face
#print axioms ThomGame.Construction.oddPathInsertedGraph_exists_euler
#print axioms ThomGame.Construction.oddInsertedDart_vertex_injective
#print axioms ThomGame.Construction.oddInsertedDart_label_injective
#print axioms ThomGame.Construction.oddInsertedDart_next_vertex
#print axioms ThomGame.Construction.oddInsertedCircuit
#print axioms ThomGame.Construction.oddInsertedHub_label
#print axioms ThomGame.Construction.oddInsertedDart_label
#print axioms ThomGame.Construction.oddInsertedCircuit_cover
#print axioms ThomGame.Construction.oddInsertedCircuit_face_of_corners
#print axioms ThomGame.Construction.oddInsertedCircuit_exists_face_and_same_face
#print axioms ThomGame.Construction.oddInsertedCircuit_exists_facial_copy
#print axioms ThomGame.Construction.oddInsertedCircuit_exists_diagram
#check ThomGame.Construction.oddInsertedCircuit_exists_face_and_same_face
#check ThomGame.Construction.oddInsertedCircuit_exists_facial_copy
#check ThomGame.Construction.oddInsertedCircuit_exists_diagram

-- Actual strict descent, exceptional-path termination, and the new character minimum.
#print ThomGame.Pictures.PortGraph.RimFacialCoverAt
#print ThomGame.Construction.OddPathGood
#print ThomGame.Construction.OddUnfinishedPath
#print ThomGame.Construction.OddRimIndependentOnly
#print ThomGame.Construction.SigmaRimPrepared
#print ThomGame.Construction.SigmaCharacterMinimalRimState
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.disjointCircuit
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.disjointCircuit_face
#print axioms ThomGame.Pictures.PortGraph.RowPairInsertion.disjointCircuit_cover
#print axioms ThomGame.Pictures.PortGraph.rimFacialCoverAt_of_marked
#print axioms ThomGame.Pictures.PortGraph.rimFacialCoverAt_iff_circuit
#print axioms ThomGame.Construction.oddInsertedSeedEquiv
#print axioms ThomGame.Construction.oddInsertedSeedPort
#print axioms ThomGame.Construction.oddPath_good_circuit_avoids_cuts
#print axioms ThomGame.Construction.oddInserted_preserves_good_seed
#print axioms ThomGame.Construction.oddInserted_selected_seed_good
#print axioms ThomGame.Construction.oddUnfinishedPathPullback_injective
#print axioms ThomGame.Construction.oddUnfinishedPathPullback_omits
#print axioms ThomGame.Construction.oddUnfinishedPathCount_insert_lt
#print axioms ThomGame.Construction.oddPathInsertion_exists_decreasing
#print axioms ThomGame.Construction.oddPath_seed_on_rim_of_covered_port
#print axioms ThomGame.Construction.oddPath_good_of_covered_port
#print axioms ThomGame.Construction.oddRim_facial_cover_or_independent
#print axioms ThomGame.Construction.exists_odd_path_normalization
#print axioms ThomGame.Construction.exists_odd_rim_normalization
#print axioms ThomGame.Construction.exists_character_minimum_of_prepared
#print axioms ThomGame.Construction.exists_character_minimal_rim_state
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_character_minimal_rim_state
#print axioms ThomGame.Construction.oddIndependent_hub_label
#print axioms ThomGame.Construction.oddIndependent_hub_port_marked
#print axioms ThomGame.Construction.oddIndependentPartner_paired
#print axioms ThomGame.Construction.oddIndependentPairing
#print axioms ThomGame.Construction.oddIndependent_length_even
#print axioms ThomGame.Construction.oddIndependent_removed_weight_zero
#print axioms ThomGame.Construction.oddIndependent_erased_weight
#check ThomGame.Construction.oddUnfinishedPathCount_insert_lt
#check ThomGame.Construction.exists_odd_rim_normalization
#check ThomGame.Construction.J_sigma_eq_one_iff_character_minimal_rim_state

-- Actual independent-rim deletion, complete rim preservation, and all facial covers.
#print ThomGame.Construction.OddIndependentCutKeep
#print ThomGame.Construction.oddIndependentCutLabel
#print ThomGame.Construction.oddIndependentCutPort
#print ThomGame.Construction.oddIndependentCutGraph
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.corner_rotation_of_boundsFaceOrbit
#print axioms ThomGame.Construction.oddIndependentCutKeep_twin
#print axioms ThomGame.Construction.oddIndependentCutLabel_twin
#print axioms ThomGame.Construction.oddIndependentCutPort_injective
#print axioms ThomGame.Construction.oddIndependentCutPort_surjective
#print axioms ThomGame.Construction.oddIndependentCutPort_label
#print axioms ThomGame.Construction.oddIndependentCutGraph_twin
#print axioms ThomGame.Construction.oddIndependentCutGraph_character
#print axioms ThomGame.Construction.oddIndependentCutGraph_hub_card_lt
#print axioms ThomGame.Construction.oddIndependentCutReturn_joint
#print axioms ThomGame.Construction.oddIndependentCutGraph_rotation
#print axioms ThomGame.Construction.oddIndependentCutGraph_euler
#print axioms ThomGame.Construction.oddIndependentErasure_euler
#print axioms ThomGame.Construction.oddIndependentErasure_character
#print axioms ThomGame.Construction.oddIndependentErasure_hub_card
#print axioms ThomGame.Construction.exists_oddIndependent_erasure
#print axioms ThomGame.Construction.oddIndependentErasurePorts_hub
#print axioms ThomGame.Construction.oddIndependentErasurePorts_rotation
#print axioms ThomGame.Construction.oddIndependentErasurePorts_vertex
#print axioms ThomGame.Construction.oddIndependentErasurePorts_label
#print axioms ThomGame.Construction.oddIndependentErasurePorts_twin
#print axioms ThomGame.Construction.oddIndependentErasurePorts_unmarked
#print axioms ThomGame.Construction.oddErasureRecoveredCircuit_port
#print axioms ThomGame.Construction.oddErasureRecoveredCircuit_label
#print axioms ThomGame.Construction.oddErasureRecoveredCircuit_face
#print axioms ThomGame.Construction.oddErasureRecoveredCircuit_cover
#print axioms ThomGame.Construction.sigmaCircuit_facial_cover_of_base
#print axioms ThomGame.Construction.oddIndependentErasure_stellar
#print axioms ThomGame.Construction.oddIndependentErasure_prepared
#print axioms ThomGame.Construction.SigmaCharacterMinimalRimState.no_independent_rim
#print axioms ThomGame.Construction.SigmaCharacterMinimalRimState.all_facial_covers
#print axioms ThomGame.Construction.exists_all_facial_covers
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_all_facial_covers
#check ThomGame.Construction.exists_oddIndependent_erasure
#check ThomGame.Construction.oddIndependentErasure_prepared
#check ThomGame.Construction.exists_all_facial_covers
#check ThomGame.Construction.J_sigma_eq_one_iff_all_facial_covers

-- Lemma 11.9: actual maximum, cover degrees, and complete private-edge surgery.
#print ThomGame.Construction.SigmaMaximalRimState
#print ThomGame.Pictures.PortGraph.SimpleCircuit.IsLabelCopy
#print ThomGame.Pictures.PortGraph.RowEdgeSwitch
#print ThomGame.Construction.SigmaRimsFacialCopies
#print axioms ThomGame.Pictures.PortGraph.totalRimCount_le_hubs
#print axioms ThomGame.Construction.exists_maximal_rim_state
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_maximal_rim_state
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cover_orientation
#print axioms ThomGame.Pictures.PermutationCover.card_eq_mul_fiber
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.cover_length_eq
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.isLabelCopy_iff_length
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.copyEdgeEquiv_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.copyVertexEquiv_label
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.noncopy_repeats_every_edge
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.twin_first
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.twin_second
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.character
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.hub_card
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_noncopy_switch
#print axioms ThomGame.Pictures.RotationEuler.joinVertex_sameFace_saturated
#print axioms ThomGame.Pictures.RotationEuler.conjugateRotation_saturated
#print axioms ThomGame.Pictures.RotationEuler.switchEdges_saturated
#print axioms ThomGame.Pictures.RotationEuler.switchEdges_twins
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.eulerDefect_of_same_face
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.eulerDefect_of_twin_face
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.eulerDefect_of_facial_cuts
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.exists_noncopy_euler_switch
#print axioms ThomGame.Pictures.PairingCycles.switchedEdge_component_card_split
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimPairing_perm
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimVertexPairing_eq
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimCount_split
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimCount_of_avoids
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimWalk_sameCycle_of_canonical_cuts
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.totalRimCount_split_private
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rim_covers
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimWalk_refines
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimCircuit_ports_subset
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rim_faces_of_refines
#print axioms ThomGame.Construction.numbered_pentagon_private_edge
#print axioms ThomGame.Construction.SigmaMaximalRimState.private_noncopy_surgery
#print axioms ThomGame.Construction.SigmaMaximalRimState.private_copies
#print axioms ThomGame.Construction.SigmaMaximalRimState.pentagon_copies
#check ThomGame.Construction.SigmaMaximalRimState.private_noncopy_surgery
#check ThomGame.Construction.SigmaMaximalRimState.private_copies
#check ThomGame.Construction.SigmaMaximalRimState.pentagon_copies

-- Figure 18: two actual reconnections and the full facial-copy normal form.
#print ThomGame.Pictures.PortGraph.RimCorner
#print ThomGame.Pictures.PortGraph.rimFaceSide
#print axioms ThomGame.Pictures.PortGraph.rimSimpleCircuit_incoming_eq
#print axioms ThomGame.Pictures.PortGraph.rimCorner_of_face
#print axioms ThomGame.Pictures.PortGraph.rim_face_of_corners
#print axioms ThomGame.Pictures.PortGraph.row_rotation_two_ne_self
#print axioms ThomGame.Pictures.PortGraph.rimCorner_unique
#print axioms ThomGame.Pictures.PortGraph.rimFaceSide_corner
#print axioms ThomGame.Pictures.PortGraph.rimFaceSide_sameCycle
#print axioms ThomGame.Pictures.PortGraph.rimFaceSide_twin
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.copy_edge_eq_of_marked_label
#print axioms ThomGame.Pictures.PortGraph.rim_components_ne_of_copies
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimFaceSide_newWalk
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rim_faces_of_same_side
#print axioms ThomGame.Pictures.PortGraph.rimSwitch_shared_ne
#print axioms ThomGame.Pictures.PortGraph.rimCorner_shared_opposite
#print axioms ThomGame.Pictures.PortGraph.rimFaceSide_shared
#print axioms ThomGame.Pictures.PairingCycles.switchedEdge_component_card_join
#print axioms ThomGame.Pictures.PairingCycles.switchedEdge_connected
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.graph_different_edges
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rim_components_join
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.rimCount_join
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.joined_rim_not_copy
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.totalRimCount_split_join
#print axioms ThomGame.Pictures.PortGraph.RowEdgeSwitch.all_rim_faces_of_oriented
#print axioms ThomGame.Construction.numbered_private_or_neighbour
#print axioms ThomGame.Construction.numbered_eq_or_eq_of_mem
#print axioms ThomGame.Construction.sigma_switch_faces_of_oriented_cuts
#print axioms ThomGame.Construction.SigmaMaximalRimState.switched_maximal
#print axioms ThomGame.Construction.SigmaMaximalRimState.shared_noncopy_first_surgery
#print axioms ThomGame.Construction.SigmaMaximalRimState.shared_noncopy_double_surgery
#print axioms ThomGame.Construction.SigmaMaximalRimState.all_facial_copies
#print axioms ThomGame.Construction.exists_all_facial_copies
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_all_facial_copies
#check ThomGame.Construction.SigmaMaximalRimState.shared_noncopy_double_surgery
#check ThomGame.Construction.SigmaMaximalRimState.all_facial_copies
#check ThomGame.Construction.exists_all_facial_copies
#check ThomGame.Construction.J_sigma_eq_one_iff_all_facial_copies
#print axioms ThomGame.Pictures.PortGraph.CycleCopyLift.hub_injective
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.copyHub_marked
#print axioms ThomGame.Pictures.PortGraph.SimpleCircuit.copyLift_hub_range
#print axioms ThomGame.Pictures.PortGraph.rimCopyLift_seed
#print axioms ThomGame.Wheel.Family.central_lift_twin
#print axioms ThomGame.Wheel.Family.pentagon_copy_twins
#print axioms ThomGame.Wheel.Family.pentagon_lift_neighbour
#print axioms ThomGame.Wheel.Family.pentagonLiftAtCentral_seed
#print axioms ThomGame.Wheel.Family.GraphLift.auxiliary_twin
#print axioms ThomGame.Wheel.Family.GraphLift.contains_of_adj
#print axioms ThomGame.Wheel.Family.GraphLift.hubs_connected
#print axioms ThomGame.Wheel.Family.GraphLift.contains_iff_connected
#print axioms ThomGame.Wheel.Family.GraphLift.unique_hub_over_row
#print axioms ThomGame.Wheel.Family.GraphLift.component_card
#print axioms ThomGame.Wheel.Family.GraphLift.component_rhs_sum
#print axioms ThomGame.Wheel.Family.exists_graphLift_containing
#print axioms ThomGame.Wheel.Family.component_one_hub_per_row
#print axioms ThomGame.Wheel.Family.every_hub_in_whole_wheel
#print axioms ThomGame.Construction.sigma_whole_wheel_component
#print axioms ThomGame.Construction.sigma_every_hub_in_whole_wheel
#print axioms ThomGame.Construction.J_sigma_eq_one_iff_whole_wheel_normal_form
#check ThomGame.Wheel.Family.WholeWheelComponent
#check ThomGame.Construction.sigma_every_hub_in_whole_wheel
#check ThomGame.Construction.J_sigma_eq_one_iff_whole_wheel_normal_form

-- Actual wheel contraction and the specified central involution of Sigma.
#print ThomGame.Wheel.Family.GraphAtlas
#print ThomGame.Wheel.Family.presentation
#print ThomGame.Wheel.Family.GraphAtlas.collapsedGraph
#print axioms ThomGame.Pictures.PortGraph.rimFaceSide_positive_turn
#print axioms ThomGame.Pictures.PortGraph.hubFlip_eq_of_facial_rim_step
#print axioms ThomGame.Wheel.Family.GraphLift.port_label
#print axioms ThomGame.Wheel.Family.GraphLift.central_flip_prev
#print axioms ThomGame.Wheel.Family.GraphLift.layer_flips
#print axioms ThomGame.Wheel.Family.GraphLift.central_flips
#print axioms ThomGame.Wheel.Family.GraphLift.hubFlip_eq
#print axioms ThomGame.Wheel.Family.GraphLift.exists_uniform_orientation
#print axioms ThomGame.Pictures.FaceReturnContraction.face_eq
#print axioms ThomGame.Pictures.FaceReturnContraction.saturated
#print axioms ThomGame.Wheel.Family.ordinaryPort_twin_iff
#print axioms ThomGame.Wheel.Family.ordinaryLabel_spec
#print axioms ThomGame.Wheel.Family.ordinaryPairing_perm
#print axioms ThomGame.Wheel.Family.ordinaryRotation_saturated
#print axioms ThomGame.Wheel.Family.ordinary_hub_iff
#print axioms ThomGame.Wheel.Family.ordinaryPort_exists_hub
#print axioms ThomGame.Wheel.Family.GraphLift.ordinary_port_iff
#print axioms ThomGame.Wheel.Family.GraphLift.ordinaryPort_label
#print axioms ThomGame.Wheel.Family.GraphLift.rotation_false
#print axioms ThomGame.Wheel.Family.GraphLift.rotation_true
#print axioms ThomGame.Wheel.Family.GraphLift.ordinaryReturn_false
#print axioms ThomGame.Wheel.Family.GraphLift.ordinaryReturn_true
#print axioms ThomGame.Wheel.Family.GraphLift.ordinaryRotation_apply
#print axioms ThomGame.Wheel.Family.GraphAtlas.hub_bijective
#print axioms ThomGame.Wheel.Family.GraphAtlas.outerPort_injective
#print axioms ThomGame.Wheel.Family.GraphAtlas.outerPort_surjective
#print axioms ThomGame.Wheel.Family.GraphAtlas.rhs_sum
#print axioms ThomGame.Wheel.Family.presentation_get
#print axioms ThomGame.Wheel.Family.finCongr_rotate
#print axioms ThomGame.Wheel.Family.finCongr_rotate_symm
#print axioms ThomGame.Wheel.Family.presentationIndex_rotate
#print axioms ThomGame.Wheel.Family.presentationIndex_rotate_symm
#print axioms ThomGame.Wheel.Family.GraphAtlas.collapsedPort_label
#print axioms ThomGame.Wheel.Family.GraphAtlas.collapsed_pairing
#print axioms ThomGame.Wheel.Family.GraphAtlas.collapsed_rotation
#print axioms ThomGame.Wheel.Family.GraphAtlas.collapsed_euler
#print axioms ThomGame.Wheel.Family.GraphAtlas.collapsed_sign
#print axioms ThomGame.Wheel.Family.exists_collapsed_graph
#print axioms ThomGame.Wheel.Family.exists_collapsed_diagram
#print axioms ThomGame.Construction.wheelFamily_presentation
#print axioms ThomGame.Construction.sigma_facial_copies_collapse
#print axioms ThomGame.Construction.sigma_facial_copies_diagram
#print axioms ThomGame.Construction.J_sigma_ne_one
#check ThomGame.Wheel.Family.exists_collapsed_graph
#check ThomGame.Construction.sigma_facial_copies_collapse
#check ThomGame.Construction.sigma_facial_copies_diagram
#check ThomGame.Construction.J_sigma_ne_one

-- Actual normalized matrix error, free-group assignments and sequence quotients.
#print ThomGame.Analysis.normalizedTrace
#print ThomGame.Analysis.hsNorm
#print ThomGame.Analysis.MatrixAssignment
#print ThomGame.Analysis.IsApproxRepresentation
#print ThomGame.Analysis.ApproximatelyTrivial
#print ThomGame.Analysis.nullUnitarySubgroup
#print ThomGame.Analysis.UnitarySequenceQuotient
#print ThomGame.Analysis.ApproximationCountersequence
#print ThomGame.Construction.SigmaApproximatelyTrivial
#print axioms ThomGame.Analysis.hsNorm_nonneg
#print axioms ThomGame.Analysis.hsNorm_add_le
#print axioms ThomGame.Analysis.hsNorm_sub_comm
#print axioms ThomGame.Analysis.hsNorm_smul
#print axioms ThomGame.Analysis.hsNorm_conjTranspose
#print axioms ThomGame.Analysis.frobenius_eq_sqrt_entries
#print axioms ThomGame.Analysis.hsNorm_eq_sqrt_entries
#print axioms ThomGame.Analysis.trace_gram
#print axioms ThomGame.Analysis.normalizedTrace_re
#print axioms ThomGame.Analysis.hsNorm_eq_sqrt_trace
#print axioms ThomGame.Analysis.hsNorm_eq_zero_iff
#print axioms ThomGame.Analysis.hsNorm_one
#print axioms ThomGame.Analysis.hsNorm_sq
#print axioms ThomGame.Analysis.hsNorm_unitary_mul
#print axioms ThomGame.Analysis.hsNorm_mul_unitary
#print axioms ThomGame.Analysis.unitaryDist_triangle
#print axioms ThomGame.Analysis.unitaryDist_mul_left
#print axioms ThomGame.Analysis.unitaryDist_mul_right
#print axioms ThomGame.Analysis.unitaryLength_inv
#print axioms ThomGame.Analysis.unitaryLength_mul_le
#print axioms ThomGame.Analysis.unitaryLength_conj
#print axioms ThomGame.Analysis.unitaryDist_eq_length
#print axioms ThomGame.Analysis.unitaryLength_eq_zero_iff
#print axioms ThomGame.Analysis.unitaryLength_le_two
#print axioms ThomGame.Analysis.unitaryLength_neg_one
#print axioms ThomGame.Analysis.assignment_eq_lift
#print axioms ThomGame.Analysis.relationDefect_le_iff
#print axioms ThomGame.Analysis.isApprox_zero_iff
#print axioms ThomGame.Analysis.assignment_descends_iff
#print axioms ThomGame.Analysis.approximatelyTrivial_no_neg_one
#print axioms ThomGame.Analysis.nullUnitarySubgroup_normal
#print axioms ThomGame.Analysis.unitarySequenceMk_eq_one_iff
#print axioms ThomGame.Analysis.unitarySequenceMk_eq_iff
#print axioms ThomGame.Analysis.unitarySequenceMk_ne_one_of_lower_bound
#print axioms ThomGame.Analysis.quotientAssignment_relation
#print axioms ThomGame.Analysis.sequenceRepresentation_mk
#print axioms ThomGame.Analysis.exists_approximationCountersequence
#print axioms ThomGame.Analysis.ApproximationCountersequence.relation_tendsto
#print axioms ThomGame.Analysis.ApproximationCountersequence.detects_in_quotient
#print axioms ThomGame.Analysis.approximatelyTrivial_of_quotient_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_tendsto
#print axioms ThomGame.Analysis.quotientRepresentation_lift
#print axioms ThomGame.Analysis.approximatelyTrivial_quotient_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_iff_quotient_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_iff_hyperfilter_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_map
#print axioms ThomGame.Analysis.approximatelyTrivial_congr
#print axioms ThomGame.Analysis.approximatelyTrivial_of_eq_one
#print axioms ThomGame.Construction.lambda_rawRelationSet_finite
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_lambda
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_iff_quotient_killed
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial_of_normalizes_centralizer
#print axioms ThomGame.Construction.sigmaApproximation_conclusion_of_lambda
#print axioms ThomGame.Analysis.rankOneMatrix_star
#print axioms ThomGame.Analysis.rankOneMatrix_square
#print axioms ThomGame.Analysis.rankOneUnitary_square
#print axioms ThomGame.Analysis.rankOneUnitary_inv
#print axioms ThomGame.Analysis.rankOneUnitary_ne_one
#print axioms ThomGame.Analysis.unitaryLength_rankOne
#print axioms ThomGame.SolutionGroup.rankOneAssignment_relator
#print axioms ThomGame.SolutionGroup.rankOneAssignment_isApprox
#print axioms ThomGame.SolutionGroup.rankOneAssignment_odd_error
#print axioms ThomGame.Construction.sigma_rankOne_approximation
#print axioms ThomGame.Construction.rankOne_tolerance_tendsto
#print axioms ThomGame.Construction.sigma_no_positive_exact_tolerance
#check ThomGame.Analysis.approximatelyTrivial_iff_hyperfilter_killed
#check ThomGame.Construction.lambdaApproximatelyTrivial_of_normalizes_centralizer
#check ThomGame.Construction.sigmaApproximation_conclusion_of_lambda
#check ThomGame.Construction.sigma_no_positive_exact_tolerance
#print axioms ThomGame.Analysis.column_square_bound
#print axioms ThomGame.Analysis.hsNorm_mul_le_left
#print axioms ThomGame.Analysis.hsNorm_mul_le_right
#print axioms ThomGame.Analysis.hsNorm_le_matrixOpNorm
#print axioms ThomGame.Analysis.boundedUnitarySequence_star_mul
#print axioms ThomGame.Analysis.matrixNullIdeal_star
#print axioms ThomGame.Analysis.matrixQuotientMk_eq_zero_iff
#print axioms ThomGame.Analysis.matrixQuotientMk_eq_iff
#print axioms ThomGame.Analysis.matrixQuotient_one_ne_zero
#print axioms ThomGame.Analysis.unitarySequenceToAlgebra_eq_one_iff
#print axioms ThomGame.Analysis.unitaryQuotientEmbedding_injective
#print axioms ThomGame.Analysis.normalizedTrace_gram
#print axioms ThomGame.Analysis.norm_trace_le_sqrt_dim_mul_frobenius
#print axioms ThomGame.Analysis.norm_normalizedTrace_le_hsNorm
#print axioms ThomGame.Analysis.norm_normalizedTrace_le_matrixOpNorm
#print axioms ThomGame.Analysis.matrixSequenceUltratrace_tendsto
#print axioms ThomGame.Analysis.matrixSequenceUltratrace_null
#print axioms ThomGame.Analysis.matrixUltratrace_one
#print axioms ThomGame.Analysis.matrixUltratrace_add
#print axioms ThomGame.Analysis.matrixUltratrace_smul
#print axioms ThomGame.Analysis.matrixUltratrace_star
#print axioms ThomGame.Analysis.matrixUltratrace_mul_comm
#print axioms ThomGame.Analysis.matrixUltratrace_gram_nonneg
#print axioms ThomGame.Analysis.matrixUltratrace_gram_im
#print axioms ThomGame.Analysis.matrixUltratrace_faithful
#print axioms ThomGame.centralizer_comap_image_of_injective
#print axioms ThomGame.normalizes_centralizer_range_of_injective
#print axioms ThomGame.Construction.unitaryQuotient_normalizes_of_matrix_normalizes
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial_of_matrix_normalizes_centralizer
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_matrix_normalizes_centralizer
#print axioms ThomGame.Analysis.matrixTraceSpace_norm_tendsto
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_injective
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_dense
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_inner
#print axioms ThomGame.Analysis.matrixTraceSpace_norm_mul_le
#print axioms ThomGame.Analysis.matrixTraceLeft_bounded
#print axioms ThomGame.Analysis.matrixLeftOperator_injective
#print axioms ThomGame.Analysis.matrixLeftOperator_star
#print axioms ThomGame.Analysis.matrixLeftRepresentation_injective
#print axioms ThomGame.Analysis.matrixLeftRepresentation_vector_trace
#print axioms ThomGame.Analysis.matrixLeftRepresentation_cyclic
#print axioms ThomGame.Analysis.matrixLeftRepresentation_separating
#check ThomGame.Analysis.unitaryQuotientEmbedding_injective
#check ThomGame.Analysis.matrixUltratrace_faithful
#check ThomGame.Analysis.matrixHilbertEmbedding_injective
#check ThomGame.Analysis.matrixLeftRepresentation
#check ThomGame.Analysis.matrixLeftRepresentation_injective
#check ThomGame.Construction.lambdaApproximatelyTrivial_of_matrix_normalizes_centralizer
#print axioms ThomGame.Analysis.matrixTraceSpace_norm_right_mul_le
#print axioms ThomGame.Analysis.matrixTraceRight_bounded
#print axioms ThomGame.Analysis.matrixRightOperator_apply
#print axioms ThomGame.Analysis.matrixLeftRight_commute
#print axioms ThomGame.Analysis.matrixRightOperator_cyclic
#print axioms ThomGame.Analysis.matrix_commuting_right_separating
#print axioms ThomGame.Analysis.matrixWOTAlgebra_isClosed
#print axioms ThomGame.Analysis.matrixWOTEmbedding_injective
#print axioms ThomGame.Analysis.matrixWOT_commutes_right
#print axioms ThomGame.Analysis.matrixWOT_separating
#print axioms ThomGame.Analysis.matrixVectorTrace_continuous
#print axioms ThomGame.Analysis.matrixVectorTrace_gram
#print axioms ThomGame.Analysis.matrixVectorTrace_mul_comm
#print axioms ThomGame.Analysis.matrixWOTTrace_one
#print axioms ThomGame.Analysis.matrixWOTTrace_embedding
#print axioms ThomGame.Analysis.matrixWOTTrace_star
#print axioms ThomGame.Analysis.matrixWOTTrace_mul_comm
#print axioms ThomGame.Analysis.matrixWOTTrace_gram_nonneg
#print axioms ThomGame.Analysis.matrixWOTTrace_gram_im
#print axioms ThomGame.Analysis.matrixWOTTrace_faithful
#print axioms ThomGame.Analysis.mul_star_eq_one_of_faithful_trace
#print axioms ThomGame.Analysis.matrixFiniteEmbedding_injective
#print axioms ThomGame.Analysis.matrixFiniteTrace_embedding
#print axioms ThomGame.Analysis.matrixFiniteTrace_mul_comm
#print axioms ThomGame.Analysis.matrixFiniteTrace_star
#print axioms ThomGame.Analysis.matrixFiniteTrace_gram_nonneg
#print axioms ThomGame.Analysis.matrixFiniteTrace_faithful
#print axioms ThomGame.Analysis.matrixFinite_isometry_unitary
#print axioms ThomGame.Analysis.matrixFinite_mem_unitary_iff
#print axioms ThomGame.Analysis.matrixUnitVector_norm
#print axioms ThomGame.Analysis.matrixFiniteTrace_norm_le
#print axioms ThomGame.Analysis.matrixFiniteTrace_norm
#print axioms ThomGame.Analysis.matrixFiniteTrace_nonneg
#print axioms ThomGame.Analysis.matrixFiniteTrace_monotone
#print axioms ThomGame.Analysis.matrixFiniteTrace_wot_tendsto
#print axioms ThomGame.Analysis.matrixFiniteUnitaryHom_injective
#print axioms ThomGame.Analysis.unitaryQuotientFiniteEmbedding_injective
#print axioms ThomGame.Analysis.unitaryQuotientFiniteEmbedding_trace
#check ThomGame.Analysis.matrixWOTAlgebra_isClosed
#check ThomGame.Analysis.matrixWOTTrace_faithful
#check ThomGame.Analysis.matrixFinite_isometry_unitary
#check ThomGame.Analysis.matrixFiniteTrace_wot_tendsto
#check ThomGame.Analysis.unitaryQuotientFiniteEmbedding_injective
section
variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)
#synth CStarAlgebra (ThomGame.Analysis.MatrixFiniteOperatorAlgebra dims hd U)
#synth CompleteSpace (ThomGame.Analysis.MatrixFiniteOperatorAlgebra dims hd U)
end

#print axioms ThomGame.Analysis.diagonalDepth_spec
#print axioms ThomGame.Analysis.diagonalDepth_tendsto
#print axioms ThomGame.Analysis.diagonalDepth_pred_eventually
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_norm_tendsto
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_dist_tendsto
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_norm_le
#print axioms ThomGame.Analysis.exists_matrixDiagonal_of_fast_approximation
#print axioms ThomGame.Analysis.matrixBoundedTraceBall_mem_of_fast_approximation
#print axioms ThomGame.Analysis.matrixBoundedTraceBall_isClosed
#print axioms ThomGame.Analysis.matrixBoundedTraceBall_isComplete
#print axioms ThomGame.Analysis.matrixBoundedTraceBall_convex
#print axioms ThomGame.Analysis.matrixBoundedTraceBall_weak_isClosed
#print axioms ThomGame.Analysis.matrixLeftRepresentation_norm_le
#print axioms ThomGame.Analysis.matrixBoundedWOTBall_norm_le
#print axioms ThomGame.Analysis.matrixBoundedWOTBall_iff
#print axioms ThomGame.Analysis.matrixWOT_apply_weak_continuous
#print axioms ThomGame.Analysis.matrixBoundedWOTBall_isClosed
#print axioms ThomGame.Analysis.matrixBoundedWOTBall_hyperfilter_isClosed
#print axioms ThomGame.Analysis.matrixRestrictedTraceSet_isClosed
#print axioms ThomGame.Analysis.matrixRestrictedTraceSet_isComplete
#print axioms ThomGame.Analysis.matrixInternalTraceBall_isClosed
#check ThomGame.Analysis.exists_matrixDiagonal_of_fast_approximation
#check ThomGame.Analysis.matrixBoundedTraceBall_isClosed
#check ThomGame.Analysis.matrixBoundedWOTBall_isClosed
#check ThomGame.Analysis.matrixBoundedWOTBall_hyperfilter_isClosed
#check ThomGame.Analysis.matrixInternalTraceBall_isClosed
section
variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (K : NNReal)
#synth CompleteSpace (ThomGame.Analysis.matrixBoundedTraceBall dims hd (Filter.hyperfilter Nat) K)
end

#print axioms ThomGame.Analysis.matrixOperatorProduct_apply_norm_le
#print axioms ThomGame.Analysis.matrixOperatorProductEquiv_apply
#print axioms ThomGame.Analysis.matrixOperatorProductEquiv_symm_apply
#print axioms ThomGame.Analysis.matrixOperatorProduct_norm_le
#print axioms ThomGame.Analysis.realNormClamp_norm_le
#print axioms ThomGame.Analysis.realNormClamp_eq_self
#print axioms ThomGame.Analysis.cstarNormClamp_selfAdjoint
#print axioms ThomGame.Analysis.cstarNormClamp_norm_le
#print axioms ThomGame.Analysis.cstarNormClamp_eq_self
#print axioms ThomGame.Analysis.map_cstarNormClamp
#print axioms ThomGame.Analysis.exists_selfAdjoint_norm_lift
#print axioms ThomGame.Analysis.exists_cstar_norm_lift
#print axioms ThomGame.Analysis.matrixProductToFinite_apply
#print axioms ThomGame.Analysis.matrixFiniteEmbedding_norm
#print axioms ThomGame.Analysis.exists_matrixRepresentative_bounded
#print axioms ThomGame.Analysis.exists_matrixRepresentative_norm_le
#print axioms ThomGame.Analysis.exists_matrixSelfAdjointRepresentative_bounded
#print axioms ThomGame.Analysis.matrixRepresentedEquiv_apply
#print axioms ThomGame.Analysis.matrixRepresentedAlgebra_isClosed
#print axioms ThomGame.Analysis.wot_norm_le_iff
#print axioms ThomGame.Analysis.wot_norm_ball_isClosed
#print axioms ThomGame.Analysis.matrixRepresentedWOTNormBall_eq
#print axioms ThomGame.Analysis.matrixRepresentedWOTNormBall_isClosed
#check ThomGame.Analysis.exists_cstar_norm_lift
#check ThomGame.Analysis.exists_matrixRepresentative_norm_le
#check ThomGame.Analysis.exists_matrixSelfAdjointRepresentative_bounded
#check ThomGame.Analysis.matrixRepresentedEquiv
#check ThomGame.Analysis.matrixRepresentedAlgebra_isClosed
#check ThomGame.Analysis.matrixRepresentedWOTNormBall_isClosed
section
variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i)
#synth CStarAlgebra (ThomGame.Analysis.MatrixOperatorProduct dims hd)
#synth CompleteSpace (ThomGame.Analysis.MatrixOperatorProduct dims hd)
end
section
variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
#synth CStarAlgebra (ThomGame.Analysis.MatrixRepresentedCStarAlgebra dims hd)
#synth CompleteSpace (ThomGame.Analysis.MatrixRepresentedCStarAlgebra dims hd)
end

#print axioms ThomGame.Analysis.positive_trace_mul_nonneg
#print axioms ThomGame.Analysis.realNormClamp_tail_sub
#print axioms ThomGame.Analysis.realUpperTail_mul_clamp
#print axioms ThomGame.Analysis.realLowerTail_mul_clamp
#print axioms ThomGame.Analysis.cstarUpperTail_nonneg
#print axioms ThomGame.Analysis.cstarLowerTail_nonneg
#print axioms ThomGame.Analysis.cstarNormClamp_tail_sub
#print axioms ThomGame.Analysis.cstarUpperTail_mul_clamp
#print axioms ThomGame.Analysis.cstarLowerTail_mul_clamp
#print axioms ThomGame.Analysis.trace_clamp_cross_nonneg
#print axioms ThomGame.Analysis.trace_clamp_sq_sub_le
#print axioms ThomGame.Analysis.matrixFiniteVector_embedding
#print axioms ThomGame.Analysis.matrixFiniteVector_inner
#print axioms ThomGame.Analysis.matrixFiniteVector_eq_zero_iff
#print axioms ThomGame.Analysis.matrixFiniteVector_injective
#print axioms ThomGame.Analysis.matrixFiniteRealTrace_nonneg
#print axioms ThomGame.Analysis.matrixFiniteRealTrace_mul_comm
#print axioms ThomGame.Analysis.matrixFiniteRealTrace_gram
#print axioms ThomGame.Analysis.matrixFiniteVector_star_norm
#print axioms ThomGame.Analysis.matrixFiniteVector_realPart_norm_le
#print axioms ThomGame.Analysis.matrixFiniteVector_realPart_dist_le
#print axioms ThomGame.Analysis.matrixFiniteVector_clamp_dist_le
#print axioms ThomGame.Analysis.matrixFinite_selfAdjoint_trace_approximation
#print axioms ThomGame.Analysis.matrixFinite_selfAdjoint_bounded_trace_approximation
#print axioms ThomGame.Analysis.matrixFinite_selfAdjoint_vector_mem_traceBall
#print axioms ThomGame.Analysis.matrixFinite_selfAdjoint_has_preimage
#print axioms ThomGame.Analysis.matrixFiniteEmbedding_surjective
#print axioms ThomGame.Analysis.matrixFiniteEquiv_trace
#print axioms ThomGame.Analysis.matrixWOTEmbedding_surjective
#print axioms ThomGame.Analysis.matrixWOTEquiv_trace
#print axioms ThomGame.Analysis.matrixLeftWOTRepresentation_range_eq
#print axioms ThomGame.Analysis.matrixLeftWOTRepresentation_range_isClosed
#print axioms ThomGame.Analysis.matrixRepresentedAlgebra_eq_operatorAlgebra
#print axioms ThomGame.Analysis.matrixFiniteEmbedding_hyperfilter_surjective
#check ThomGame.Analysis.trace_clamp_sq_sub_le
#check ThomGame.Analysis.matrixFinite_selfAdjoint_bounded_trace_approximation
#check ThomGame.Analysis.matrixFiniteEmbedding_surjective
#check ThomGame.Analysis.matrixFiniteEquiv
#check ThomGame.Analysis.matrixWOTEquiv
#check ThomGame.Analysis.matrixLeftWOTRepresentation_range_isClosed
#check ThomGame.Analysis.matrixFiniteEmbedding_hyperfilter_surjective
section
variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)
#synth StarOrderedRing (ThomGame.Analysis.MatrixFiniteOperatorAlgebra dims hd U)
end

#print axioms ThomGame.Analysis.matrixInternalProduct_isClosed
#print axioms ThomGame.Analysis.matrixInternalProductToQuotient_range
#print axioms ThomGame.Analysis.exists_matrixInternalRepresentative_bounded
#print axioms ThomGame.Analysis.exists_matrixInternalSelfAdjointRepresentative_bounded
#print axioms ThomGame.Analysis.matrixInternalTraceVectors_convex
#print axioms ThomGame.Analysis.matrixInternalWOT_vector_mem_closure
#print axioms ThomGame.Analysis.matrixInternal_selfAdjoint_bounded_trace_approximation
#print axioms ThomGame.Analysis.matrixInternal_selfAdjoint_vector_mem_traceBall
#print axioms ThomGame.Analysis.matrixInternal_selfAdjoint_has_preimage
#print axioms ThomGame.Analysis.matrixInternal_has_preimage
#print axioms ThomGame.Analysis.matrixInternalWOTAlgebra_closure_eq
#print axioms ThomGame.Analysis.matrixInternalWOTAlgebra_isClosed
#print axioms ThomGame.Analysis.matrixInternalWOTClosureEmbedding_injective
#print axioms ThomGame.Analysis.matrixInternalWOTClosureEmbedding_surjective
#print axioms ThomGame.Analysis.matrixInternalWOTAlgebra_hyperfilter_isClosed
#print axioms ThomGame.Analysis.matrixInternalFiniteAlgebra_isClosed
#print axioms ThomGame.Analysis.matrixInternalFiniteEmbedding_bijective
#print axioms ThomGame.Analysis.matrixInternalFiniteEquiv_trace
#print axioms ThomGame.Analysis.matrixInternalFiniteTrace_faithful
#print axioms ThomGame.Analysis.matrixInternalWOTEquiv_trace
#check ThomGame.Analysis.exists_matrixInternalSelfAdjointRepresentative_bounded
#check ThomGame.Analysis.matrixInternal_selfAdjoint_bounded_trace_approximation
#check ThomGame.Analysis.matrixInternalWOTAlgebra_isClosed
#check ThomGame.Analysis.matrixInternalWOTEquiv
#check ThomGame.Analysis.matrixInternalFiniteAlgebra_isClosed
#check ThomGame.Analysis.matrixInternalWOTEquiv_trace
section
variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (ThomGame.Analysis.CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n)
#synth CStarAlgebra (ThomGame.Analysis.MatrixInternalProduct dims S hd)
#synth CompleteSpace (ThomGame.Analysis.MatrixInternalProduct dims S hd)
#synth CStarAlgebra (ThomGame.Analysis.MatrixInternalFiniteCStarAlgebra dims S hd)
#synth CompleteSpace (ThomGame.Analysis.MatrixInternalFiniteCStarAlgebra dims S hd)
end

#print axioms ThomGame.Analysis.positive_operator_sq_le
#print axioms ThomGame.Analysis.positive_operator_apply_norm_sq_le
#print axioms ThomGame.Analysis.wot_nonneg_isClosed
#print axioms ThomGame.Analysis.wot_le_isClosed
#print axioms ThomGame.Analysis.wot_ge_isClosed
#print axioms ThomGame.Analysis.monotone_positive_operator_apply_cauchy
#print axioms ThomGame.Analysis.exists_monotone_positive_operator_limit
#print axioms ThomGame.Analysis.exists_directed_sup_of_positive_sup
#print axioms ThomGame.Analysis.exists_positive_sup_in_wot_closed_subalgebra
#print axioms ThomGame.Analysis.exists_directed_sup_in_wot_closed_subalgebra
#print axioms ThomGame.Analysis.exists_matrixFinite_positive_sup
#print axioms ThomGame.Analysis.matrixFinite_positive_tendsto_sup
#print axioms ThomGame.Analysis.exists_matrixFinite_directed_sup
#print axioms ThomGame.Analysis.matrixFiniteTrace_preserves_positive_sup
#print axioms ThomGame.Analysis.matrixFiniteRealTrace_sup_eq_ciSup
#print axioms ThomGame.Analysis.matrixFiniteTrace_normal
#print axioms ThomGame.Analysis.exists_matrixInternalFinite_positive_sup
#print axioms ThomGame.Analysis.matrixInternalFinite_positive_tendsto_sup
#print axioms ThomGame.Analysis.matrixInternalFiniteTrace_preserves_positive_sup
#print axioms ThomGame.Analysis.matrixInternalFiniteTrace_re_sup_eq_ciSup
#print axioms ThomGame.Analysis.exists_matrixInternalFinite_directed_sup
#print axioms ThomGame.Analysis.matrixInternalFiniteTrace_normal
#check ThomGame.Analysis.exists_monotone_positive_operator_limit
#check ThomGame.Analysis.exists_matrixFinite_directed_sup
#check ThomGame.Analysis.matrixFiniteTrace_normal
#check ThomGame.Analysis.matrixFiniteRealTrace_sup_eq_ciSup
#check ThomGame.Analysis.matrixInternalFinite_positive_tendsto_sup
#check ThomGame.Analysis.exists_matrixInternalFinite_directed_sup
#check ThomGame.Analysis.matrixInternalFiniteTrace_normal

#print axioms ThomGame.Analysis.finiteMatrixHilbert_inner
#print axioms ThomGame.Analysis.finiteMatrixHilbert_norm
#print axioms ThomGame.Analysis.matrixTraceProjection_unique
#print axioms ThomGame.Analysis.matrixTraceProjection_pairing
#print axioms ThomGame.Analysis.matrixTraceProjection_bimodule
#print axioms ThomGame.Analysis.matrixTraceProjection_star
#print axioms ThomGame.Analysis.matrixTraceProjection_nonneg
#print axioms ThomGame.Analysis.matrixTraceProjection_schwarz
#print axioms ThomGame.Analysis.matrixTraceProjection_matrixOpNorm_le
#print axioms ThomGame.Analysis.matrixSequenceExpectation_null
#print axioms ThomGame.Analysis.matrixSequenceExpectation_pairing
#print axioms ThomGame.Analysis.matrixQuotientExpectation_range
#print axioms ThomGame.Analysis.matrixQuotientExpectation_bimodule
#print axioms ThomGame.Analysis.matrixQuotientExpectation_trace
#print axioms ThomGame.Analysis.matrixQuotientExpectation_unique
#print axioms ThomGame.Analysis.matrixQuotientExpectation_hilbertNorm_le
#print axioms ThomGame.Analysis.matrixHilbertExpectation_embedding
#print axioms ThomGame.Analysis.matrixHilbertExpectation_range
#print axioms ThomGame.Analysis.matrixQuotientExpectation_pythagoras
#print axioms ThomGame.Analysis.matrixQuotientExpectation_bestApproximation
#check ThomGame.Analysis.matrixTraceProjection_schwarz
#check ThomGame.Analysis.matrixTraceProjection_matrixOpNorm_le
#check ThomGame.Analysis.matrixQuotientExpectation_unique
#check ThomGame.Analysis.matrixHilbertExpectation_embedding
#check ThomGame.Analysis.matrixQuotientExpectation_bestApproximation

#print axioms ThomGame.Analysis.eq_zero_of_nonneg_of_faithful_trace
#print axioms ThomGame.Analysis.eq_of_le_of_faithful_trace
#print axioms ThomGame.Analysis.trace_projection_nonneg
#print axioms ThomGame.Analysis.norm_le_of_unital_schwarz
#print axioms ThomGame.Analysis.matrixFiniteExpectation_embedding
#print axioms ThomGame.Analysis.matrixFiniteExpectation_range
#print axioms ThomGame.Analysis.matrixFiniteExpectation_bimodule
#print axioms ThomGame.Analysis.matrixFiniteExpectation_trace
#print axioms ThomGame.Analysis.matrixFiniteExpectation_pairing
#print axioms ThomGame.Analysis.matrixFiniteExpectation_vector
#print axioms ThomGame.Analysis.matrixFiniteExpectation_nonneg
#print axioms ThomGame.Analysis.matrixFiniteExpectation_schwarz
#print axioms ThomGame.Analysis.matrixFiniteExpectation_norm_le
#print axioms ThomGame.Analysis.matrixFiniteExpectationCLM_norm
#print axioms ThomGame.Analysis.matrixFiniteExpectation_faithful
#print axioms ThomGame.Analysis.matrixFiniteExpectation_nonneg_eq_zero_iff
#print axioms ThomGame.Analysis.matrixInternalExpectation_eq_self
#print axioms ThomGame.Analysis.matrixInternalExpectation_trace
#print axioms ThomGame.Analysis.matrixFiniteExpectation_preserves_positive_sup
#print axioms ThomGame.Analysis.matrixFiniteExpectation_positive_tendsto_sup
#print axioms ThomGame.Analysis.matrixInternalExpectation_preserves_positive_sup
#print axioms ThomGame.Analysis.matrixFiniteExpectation_normal
#print axioms ThomGame.Analysis.cstarRightNormClamp_gram
#print axioms ThomGame.Analysis.cstarRightNormClamp_norm_le
#print axioms ThomGame.Analysis.cstarRightNormClamp_eq_self
#print axioms ThomGame.Analysis.map_cstarRightNormClamp
#print axioms ThomGame.Analysis.exists_cstar_exact_norm_lift
#print axioms ThomGame.Analysis.exists_matrixRepresentative_bounded_exact
#print axioms ThomGame.Analysis.exists_matrixInternalRepresentative_bounded_exact
#print axioms ThomGame.Analysis.exists_matrixFiniteRepresentative_bounded
#print axioms ThomGame.Analysis.exists_matrixInternalFiniteRepresentative_bounded
#check ThomGame.Analysis.matrixFiniteExpectation_nonneg
#check ThomGame.Analysis.matrixFiniteExpectationCLM_norm
#check ThomGame.Analysis.matrixFiniteExpectation_normal
#check ThomGame.Analysis.matrixInternalExpectation_preserves_positive_sup
#check ThomGame.Analysis.exists_cstar_exact_norm_lift
#check ThomGame.Analysis.exists_matrixRepresentative_bounded_exact
#check ThomGame.Analysis.exists_matrixInternalRepresentative_bounded_exact
#check ThomGame.Analysis.exists_matrixFiniteRepresentative_bounded

#print axioms ThomGame.Analysis.hsNorm_apply_le_matrixMixedNorm
#print axioms ThomGame.Analysis.matrixMixedNorm_le
#print axioms ThomGame.Analysis.exists_matrixMixedNorm_maximizer
#print axioms ThomGame.Analysis.UniformMatrixMap.sequenceMap_null
#print axioms ThomGame.Analysis.UniformMatrixMap.sub_quotientMap
#print axioms ThomGame.Analysis.UniformMatrixMap.comp_quotientMap
#print axioms ThomGame.Analysis.UniformMatrixMap.traceSpace_norm_le
#print axioms ThomGame.Analysis.UniformMatrixMap.hilbertMap_embedding
#print axioms ThomGame.Analysis.UniformMatrixMap.hilbertMap_norm_le
#print axioms ThomGame.Analysis.UniformMatrixMap.finiteMap_norm_le
#print axioms ThomGame.Analysis.UniformMatrixMap.finiteToHilbert_vector
#print axioms ThomGame.Analysis.UniformMatrixMap.sub_finiteToHilbert
#print axioms ThomGame.Analysis.UniformMatrixMap.exists_maximizingSequence
#print axioms ThomGame.Analysis.UniformMatrixMap.coordinateMixedNorm_tendsto
#print axioms ThomGame.Analysis.UniformMatrixMap.finiteToHilbert_apply_norm_le_limit
#print axioms ThomGame.Analysis.UniformMatrixMap.finiteToHilbert_norm_eq_limit
#print axioms ThomGame.Analysis.UniformMatrixMap.coordinateMixedNorm_tendsto_norm
#print axioms ThomGame.Analysis.UniformMatrixMap.quotientMap_eq_zero_iff_mixedNorm_tendsto_zero
#print axioms ThomGame.Analysis.UniformMatrixMap.quotientMap_eq_iff_mixedNorm_sub_tendsto_zero
#print axioms ThomGame.Analysis.matrixUniformExpectation_quotientMap
#print axioms ThomGame.Analysis.matrixUniformExpectation_hilbertMap
#print axioms ThomGame.Analysis.matrixUniformExpectation_finiteMap
#print axioms ThomGame.Analysis.matrixUniformExpectation_finiteCLM
#print axioms ThomGame.Analysis.quotientMap_eq_expectation_iff_mixedNorm_tendsto_zero
#print axioms ThomGame.Analysis.finiteMap_eq_expectation_iff_mixedNorm_tendsto_zero
#print axioms ThomGame.Analysis.quotientRange_eq_internal_iff_mixedNorm_tendsto_zero
#check ThomGame.Analysis.matrixMixedNorm
#check ThomGame.Analysis.exists_matrixMixedNorm_maximizer
#check ThomGame.Analysis.UniformMatrixMap
#check ThomGame.Analysis.UniformMatrixMap.finiteToHilbert_norm_eq_limit
#check ThomGame.Analysis.UniformMatrixMap.quotientMap_eq_zero_iff_mixedNorm_tendsto_zero
#check ThomGame.Analysis.UniformMatrixMap.quotientMap_eq_iff_mixedNorm_sub_tendsto_zero
#check ThomGame.Analysis.matrixUniformExpectation
#check ThomGame.Analysis.finiteMap_eq_expectation_iff_mixedNorm_tendsto_zero
#check ThomGame.Analysis.quotientRange_eq_internal_iff_mixedNorm_tendsto_zero

#print axioms ThomGame.Analysis.matrixUnitaryConjugation_matrixOpNorm
#print axioms ThomGame.Analysis.matrixUnitaryConjugation_hsNorm
#print axioms ThomGame.Analysis.matrixUnitaryConjugation_pairing
#print axioms ThomGame.Analysis.matrixUnitaryConjugation_sub_hsNorm
#print axioms ThomGame.Analysis.matrixConjugationHilbert_pairing
#print axioms ThomGame.Analysis.matrixConjugationHilbertEquiv_symm_apply
#print axioms ThomGame.Analysis.lazyHilbertAverage_norm_le
#print axioms ThomGame.Analysis.lazyHilbertAverage_symmetric
#print axioms ThomGame.Analysis.lazyHilbertAverage_positive_form
#print axioms ThomGame.Analysis.lazyHilbertAverage_energy
#print axioms ThomGame.Analysis.lazyHilbertAverage_nonneg
#print axioms ThomGame.Analysis.lazyHilbertAverage_le_one
#print axioms ThomGame.Analysis.lazyHilbertAverage_fixed_iff
#print axioms ThomGame.Analysis.lazyHilbertAverage_defect_norm_sq_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_nonneg
#print axioms ThomGame.Analysis.matrixLazyMarkov_matrixOpNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_hilbert
#print axioms ThomGame.Analysis.matrixLazyMarkov_hsNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_pairing
#print axioms ThomGame.Analysis.matrixLazyMarkov_energy
#print axioms ThomGame.Analysis.matrixLazyMarkov_defect_norm_sq_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_trace_positive
#print axioms ThomGame.Analysis.matrixLazyMarkov_trace_defect_positive
#print axioms ThomGame.Analysis.matrixLazyMarkov_fixed_iff
#print axioms ThomGame.Analysis.matrixLazyMarkov_one
#print axioms ThomGame.Analysis.matrixLazyMarkov_trace
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_matrixOpNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_hsNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_hilbert
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_hilbertNorm_le
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_quotient_one
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_quotient_star
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_quotient_trace
#print axioms ThomGame.Analysis.UniformMatrixMap.hilbertMap_nonneg_of_trace_positive
#print axioms ThomGame.Analysis.UniformMatrixMap.hilbertMap_le_one_of_trace_defect_positive
#print axioms ThomGame.Analysis.matrixMarkovEnergy_tendsto
#print axioms ThomGame.Analysis.matrixQuotientLazyMarkov_energy
#print axioms ThomGame.Analysis.matrixQuotientLazyMarkov_defect_norm_sq_le
#print axioms ThomGame.Analysis.matrixMarkovEnergy_eq_zero_iff
#print axioms ThomGame.Analysis.matrixQuotientLazyMarkov_fixed_iff
#print axioms ThomGame.Analysis.matrixLazyMarkov_hilbertMap_nonneg
#print axioms ThomGame.Analysis.matrixLazyMarkov_hilbertMap_le_one
#print axioms ThomGame.Analysis.matrixLazyMarkov_hilbertMap_selfAdjoint
#print axioms ThomGame.Analysis.matrixFiniteLazyMarkov_fixed_iff
#check ThomGame.Analysis.lazyHilbertAverage
#check ThomGame.Analysis.lazyHilbertAverage_energy
#check ThomGame.Analysis.lazyHilbertAverage_defect_norm_sq_le
#check ThomGame.Analysis.matrixLazyMarkov
#check ThomGame.Analysis.matrixLazyMarkov_energy
#check ThomGame.Analysis.matrixLazyMarkov_fixed_iff
#check ThomGame.Analysis.matrixUniformMarkovPower
#check ThomGame.Analysis.matrixUniformMarkovPower_quotient_trace
#check ThomGame.Analysis.matrixMarkovEnergy
#check ThomGame.Analysis.matrixQuotientLazyMarkov_energy
#check ThomGame.Analysis.matrixQuotientLazyMarkov_fixed_iff
#check ThomGame.Analysis.matrixLazyMarkov_hilbertMap_nonneg
#check ThomGame.Analysis.matrixLazyMarkov_hilbertMap_le_one
#check ThomGame.Analysis.matrixFiniteLazyMarkov_fixed_iff
#print axioms ThomGame.Analysis.meanProjection_norm_le
#print axioms ThomGame.Analysis.meanProjection_fixed
#print axioms ThomGame.Analysis.meanProjection_eq_self_iff
#print axioms ThomGame.Analysis.meanProjection_tendsto
#print axioms ThomGame.Analysis.birkhoffAverage_mem_invariant_convex
#print axioms ThomGame.Analysis.meanProjection_mem_invariant_closed_convex
#print axioms ThomGame.Analysis.matrixMarkovProjection_norm_le
#print axioms ThomGame.Analysis.matrixMarkovProjection_fixed
#print axioms ThomGame.Analysis.matrixMarkovProjection_eq_self_iff
#print axioms ThomGame.Analysis.matrixLazyMarkov_mapsTo_boundedTraceBall
#print axioms ThomGame.Analysis.matrixMarkovProjection_mem_boundedTraceBall
#print axioms ThomGame.Analysis.exists_matrixMarkovProjection_representative
#print axioms ThomGame.Analysis.exists_matrixMarkovProjection_element
#print axioms ThomGame.Analysis.matrixTupleClass_unitary
#print axioms ThomGame.Analysis.mem_matrixRelativeCommutant_iff
#print axioms ThomGame.Analysis.matrixHilbertEmbedding_mem_relativeCommutantTraceSubspace
#print axioms ThomGame.Analysis.matrixQuotientLazyMarkov_fixed_iff_mem
#print axioms ThomGame.Analysis.matrixRelativeCommutantTraceSubspace_le_fixed
#print axioms ThomGame.Analysis.matrixMarkovProjection_mem_relativeCommutantTraceSubspace
#print axioms ThomGame.Analysis.matrixRelativeCommutantTraceSubspace_eq_fixed
#print axioms ThomGame.Analysis.matrixMarkovProjection_eq_relativeCommutantProjection
#print axioms ThomGame.Analysis.matrixRelativeProjectionElement_spec
#print axioms ThomGame.Analysis.matrixRelativeExpectation_embedding
#print axioms ThomGame.Analysis.matrixRelativeExpectation_mem
#print axioms ThomGame.Analysis.matrixRelativeExpectation_operatorNorm_le
#print axioms ThomGame.Analysis.matrixRelativeExpectation_eq_self
#print axioms ThomGame.Analysis.matrixRelativeExpectation_eq_self_iff
#print axioms ThomGame.Analysis.matrixRelativeExpectation_range
#print axioms ThomGame.Analysis.matrixRelativeExpectation_one
#print axioms ThomGame.Analysis.matrixRelativeExpectation_idem
#print axioms ThomGame.Analysis.matrixRelativeExpectation_pairing
#print axioms ThomGame.Analysis.matrixRelativeExpectation_trace
#print axioms ThomGame.Analysis.matrixRelativeExpectation_unique
#print axioms ThomGame.Analysis.matrixRelativeExpectation_star
#print axioms ThomGame.Analysis.matrixRelativeExpectation_mul_left
#print axioms ThomGame.Analysis.matrixRelativeExpectation_mul_right
#print axioms ThomGame.Analysis.matrixRelativeExpectation_bimodule
#print axioms ThomGame.Analysis.matrixRelativeExpectation_hilbertNorm_le
#print axioms ThomGame.Analysis.matrixRelativeExpectation_pythagoras
#print axioms ThomGame.Analysis.matrixRelativeExpectation_residualNorm_le
#print axioms ThomGame.Analysis.matrixRelativeExpectation_bestApproximation
#print axioms ThomGame.Analysis.matrixRelativeExpectation_cesaro_tendsto
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_embedding
#print axioms ThomGame.Analysis.matrixFiniteEmbedding_mem_relativeCommutant_iff
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_mem
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_eq_self
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_eq_self_iff
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_range
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_one
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_idem
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_star
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_mul_left
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_mul_right
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_bimodule
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_trace
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_pairing
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_vector
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_nonneg
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_monotone
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_schwarz
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_norm_le
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectationCLM_apply
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectationCLM_norm
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_realTrace
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_faithful
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_nonneg_eq_zero_iff
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_preserves_positive_sup
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_positive_tendsto_sup
#print axioms ThomGame.Analysis.matrixFiniteRelativeExpectation_normal
#print axioms ThomGame.Analysis.meanProjection_isStarProjection
#print axioms ThomGame.Analysis.mul_meanProjection
#print axioms ThomGame.Analysis.meanProjection_mul
#print axioms ThomGame.Analysis.meanProjection_residual_compression
#print axioms ThomGame.Analysis.meanProjection_residual_nonneg
#print axioms ThomGame.Analysis.meanProjection_residual_pairing
#print axioms ThomGame.Analysis.meanProjection_complement_norm_le
#print axioms ThomGame.Analysis.meanProjection_residual_norm_le
#print axioms ThomGame.Analysis.meanProjection_residual_pow
#print axioms ThomGame.Analysis.spectralGap_pow_sub_projection_norm_le
#print axioms ThomGame.Analysis.spectralGap_pow_sub_pow_norm_le
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_sequence_succ
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_quotient_const
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_hilbert_const
#print axioms ThomGame.Analysis.matrixMarkov_pow_sub_projection_norm_le
#print axioms ThomGame.Analysis.matrixMarkov_pow_sub_pow_norm_le
#print axioms ThomGame.Analysis.matrixMarkov_pow_expectation_error
#print axioms ThomGame.Analysis.matrixMarkov_powerDifference_finiteToHilbert_norm_le
#print axioms ThomGame.Analysis.matrixMarkov_powerDifference_mixedNormLimit_le
#check ThomGame.Analysis.matrixRelativeCommutant
#check ThomGame.Analysis.matrixRelativeCommutantTraceSubspace_eq_fixed
#check ThomGame.Analysis.exists_matrixMarkovProjection_element
#check ThomGame.Analysis.matrixRelativeExpectation
#check ThomGame.Analysis.matrixRelativeExpectation_embedding
#check ThomGame.Analysis.matrixRelativeExpectation_operatorNorm_le
#check ThomGame.Analysis.matrixRelativeExpectation_unique
#check ThomGame.Analysis.matrixFiniteRelativeExpectation_nonneg
#check ThomGame.Analysis.matrixFiniteRelativeExpectation_normal
#check ThomGame.Analysis.spectralGap_pow_sub_projection_norm_le
#check ThomGame.Analysis.spectralGap_pow_sub_pow_norm_le
#check ThomGame.Analysis.MatrixMarkovSpectralGap
#check ThomGame.Analysis.matrixMarkov_pow_sub_projection_norm_le
#check ThomGame.Analysis.matrixMarkov_powerDifference_mixedNormLimit_le
#print axioms ThomGame.Analysis.positiveDiagonalDepth_pos
#print axioms ThomGame.Analysis.positiveDiagonalDepth_tendsto
#print axioms ThomGame.Analysis.positiveDiagonalDepth_spec_eventually
#print axioms ThomGame.Analysis.matrixMarkovDiagonalPower_pos
#print axioms ThomGame.Analysis.matrixMarkovPowerDistance_eventually_le
#print axioms ThomGame.Analysis.matrixMarkovDiagonalRequirements_eventually
#print axioms ThomGame.Analysis.matrixMarkovDiagonalPower_tendsto
#print axioms ThomGame.Analysis.matrixMarkovDiagonalPower_spec_eventually
#print axioms ThomGame.Analysis.matrixMarkovDiagonalPower_tolerance_tendsto
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_difference_mixedNormLimit_le
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_difference_finiteToHilbert_norm_le
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_power_error
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_expectation_error
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_quotientMap_eq_expectation
#print axioms ThomGame.Analysis.matrixMarkovDiagonalPower_quotientMap_eq_expectation
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_finiteMap_eq_expectation
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_hilbertMap_eq_projection
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_range
#print axioms ThomGame.Analysis.matrixMarkov_subDiagonal_internal_iff
#print axioms ThomGame.Analysis.matrixMarkovDiagonalPower_internal_iff
#print axioms ThomGame.Analysis.exists_matrixMarkovDiagonal_inducing_expectation
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_nonneg
#print axioms ThomGame.Analysis.continuous_hsNorm
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_continuous
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_le_hsNorm_sq
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_sqrt_le_hsNorm
#print axioms ThomGame.Analysis.meanProjection_defect_pairing
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_tendsto
#print axioms ThomGame.Analysis.matrixMarkovEnergy_hilbert
#print axioms ThomGame.Analysis.matrixRelativeExpectation_energy_zero
#print axioms ThomGame.Analysis.matrixRelativeExpectation_residual_energy
#print axioms ThomGame.Analysis.matrixRelativeExpectation_poincare_sq
#print axioms ThomGame.Analysis.matrixRelativeExpectation_poincare
#print axioms ThomGame.Analysis.matrixMarkovDefect_nonneg
#print axioms ThomGame.Analysis.matrixMarkovDefect_continuous
#print axioms ThomGame.Analysis.exists_matrixMarkovDefect_maximizer
#print axioms ThomGame.Analysis.matrixMarkovDefectMaximizer_norm_le
#print axioms ThomGame.Analysis.matrixMarkovDefect_le_bound
#print axioms ThomGame.Analysis.matrixMarkovDefectBound_nonneg
#print axioms ThomGame.Analysis.matrixMarkovDefectBound_distance
#print axioms ThomGame.Analysis.matrixMarkovDefectBound_energy
#print axioms ThomGame.Analysis.matrixMarkovDefect_le_two
#print axioms ThomGame.Analysis.matrixMarkovDefectBound_le_two
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_eq_witness
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_nonneg
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_le_two
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_distance
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_energy
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_tendsto_zero_of_quotientMap_eq
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_subDiagonal_tendsto_zero
#print axioms ThomGame.Analysis.matrixUniformMarkovDefect_diagonal_tendsto_zero
#print axioms ThomGame.Analysis.matrixMarkovTolerance_pos
#print axioms ThomGame.Analysis.matrixMarkovTolerance_sqrt_bound
#print axioms ThomGame.Analysis.matrixMarkovTolerance_depth_bound
#print axioms ThomGame.Analysis.matrixMarkovTolerance_index_bound
#print axioms ThomGame.Analysis.matrixMarkovTolerance_defect_sq_bound
#print axioms ThomGame.Analysis.matrixMarkovTolerance_defect_bound
#print axioms ThomGame.Analysis.matrixMarkovTolerance_tendsto_zero
#check ThomGame.Analysis.matrixMarkovDiagonalPower_tendsto
#check ThomGame.Analysis.matrixMarkov_subDiagonal_quotientMap_eq_expectation
#check ThomGame.Analysis.matrixMarkov_subDiagonal_hilbertMap_eq_projection
#check ThomGame.Analysis.matrixMarkovDiagonalPower_internal_iff
#check ThomGame.Analysis.exists_matrixMarkovDiagonal_inducing_expectation
#check ThomGame.Analysis.matrixRelativeExpectation_poincare_sq
#check ThomGame.Analysis.matrixRelativeExpectation_poincare
#check ThomGame.Analysis.matrixMarkovDefect
#check ThomGame.Analysis.matrixMarkovDefectBound
#check ThomGame.Analysis.matrixUniformMarkovDefect_diagonal_tendsto_zero
#check ThomGame.Analysis.matrixMarkovTolerance
#check ThomGame.Analysis.matrixMarkovTolerance_defect_sq_bound
#check ThomGame.Analysis.matrixMarkovTolerance_tendsto_zero

#print axioms ThomGame.Analysis.matrixUnitaryConjugation_mul
#print axioms ThomGame.Analysis.matrixConjugateUnitary_val
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_conjugate
#print axioms ThomGame.Analysis.matrixUnitary_row_norm_sq_sum
#print axioms ThomGame.Analysis.matrixUnitary_col_norm_sq_sum
#print axioms ThomGame.Analysis.matrixEnergyWeight_nonneg
#print axioms ThomGame.Analysis.matrix_diagonal_commutator_entry
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_diagonal
#print axioms ThomGame.Analysis.matrixEnergyWeight_row_sum
#print axioms ThomGame.Analysis.matrixEnergyWeight_col_sum
#print axioms ThomGame.Analysis.matrixEnergyWeight_total
#print axioms ThomGame.Analysis.spectralStep_nonneg
#print axioms ThomGame.Analysis.spectralStep_sq
#print axioms ThomGame.Analysis.spectralStep_sq_sub
#print axioms ThomGame.Analysis.spectralStep_sq_sub_integrable
#print axioms ThomGame.Analysis.spectralStep_sq_sub_integral
#print axioms ThomGame.Analysis.spectralStep_sq_sub_intervalIntegral_le
#print axioms ThomGame.Analysis.exists_le_intervalIntegral_average
#print axioms ThomGame.Analysis.weighted_abs_sum_sq_le
#print axioms ThomGame.Analysis.weighted_spectralStep_intervalIntegrable
#print axioms ThomGame.Analysis.weighted_spectralStep_coarea
#print axioms ThomGame.Analysis.matrix_cfc_conjugate
#print axioms ThomGame.Analysis.matrixSpectralCut_eq_conjugate
#print axioms ThomGame.Analysis.matrix_diagonal_spectralStep_projection
#print axioms ThomGame.Analysis.matrixSpectralCut_isStarProjection
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_cfc
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_spectral
#print axioms ThomGame.Analysis.matrixSpectralCut_energy
#print axioms ThomGame.Analysis.normalizedTrace_diagonal_real
#print axioms ThomGame.Analysis.matrixSpectralCut_trace
#print axioms ThomGame.Analysis.normalizedTrace_eq_eigenvalue_sum
#print axioms ThomGame.Analysis.matrixSpectralCut_energy_intervalIntegrable
#print axioms ThomGame.Analysis.matrixSpectralCut_coarea
#print axioms ThomGame.Analysis.exists_matrixSpectralCut_energy_le
#print axioms ThomGame.Analysis.spectralActiveWeight_nonneg
#print axioms ThomGame.Analysis.spectralActiveWeight_le
#print axioms ThomGame.Analysis.spectralActiveWeight_le_steps
#print axioms ThomGame.Analysis.spectralActiveWeight_energy_eq
#print axioms ThomGame.Analysis.spectralStep_mul_le
#print axioms ThomGame.Analysis.weighted_spectralStep_coarea_of_mass_le
#print axioms ThomGame.Analysis.matrixEnergyWeight_step_sum
#print axioms ThomGame.Analysis.matrixEnergyWeight_active_mass_le
#print axioms ThomGame.Analysis.matrixEnergyWeight_active_mass_trace_le
#print axioms ThomGame.Analysis.matrixSpectralActiveMass_le
#print axioms ThomGame.Analysis.matrixFamilySpectralCut_energy_intervalIntegrable
#print axioms ThomGame.Analysis.matrixFamilySpectralCut_coarea
#print axioms ThomGame.Analysis.exists_matrixFamilySpectralCut_energy_le
#print axioms ThomGame.Analysis.matrixSpectralInterval_one_eq_cut
#print axioms ThomGame.Analysis.matrixFamilySpectralInterval_coarea
#print axioms ThomGame.Analysis.exists_matrixFamilySpectralInterval_energy_le
#print axioms ThomGame.Analysis.hsNorm_sub_sq_selfAdjoint
#print axioms ThomGame.Analysis.hsNorm_projection_sq
#print axioms ThomGame.Analysis.matrixProjection_diagonal_bounds
#print axioms ThomGame.Analysis.normalizedTrace_diagonal_mul_real
#print axioms ThomGame.Analysis.hsNorm_diagonal_sub_projection_sq
#print axioms ThomGame.Analysis.matrixProjection_trace_difference_le
#print axioms ThomGame.Analysis.spectralStep_projection_distance_le
#print axioms ThomGame.Analysis.hsNorm_diagonal_spectralStep_sub_projection_le
#print axioms ThomGame.Analysis.matrixSpectralCut_distance_le
#print axioms ThomGame.Analysis.matrixSpectralInterval_distance_le
#print axioms ThomGame.Analysis.exists_matrixSpectralCut_thirds_energy_le
#print axioms ThomGame.Analysis.exists_matrixProjection_improvement_of_estimates
#check ThomGame.Analysis.matrixSpectralCut
#check ThomGame.Analysis.matrixSpectralInterval
#check ThomGame.Analysis.matrixSpectralCut_isStarProjection
#check ThomGame.Analysis.matrixSpectralCut_coarea
#check ThomGame.Analysis.matrixFamilySpectralCut_coarea
#check ThomGame.Analysis.matrixFamilySpectralInterval_coarea
#check ThomGame.Analysis.exists_matrixFamilySpectralInterval_energy_le
#check ThomGame.Analysis.matrixSpectralCut_distance_le
#check ThomGame.Analysis.matrixProjection_trace_difference_le
#check ThomGame.Analysis.exists_matrixProjection_improvement_of_estimates

#print axioms ThomGame.Analysis.finiteSign_not
#print axioms ThomGame.Analysis.finiteSign_sq
#print axioms ThomGame.Analysis.finiteSignFlip_same
#print axioms ThomGame.Analysis.finiteSignFlip_other
#print axioms ThomGame.Analysis.finiteSign_expect_mul_ne
#print axioms ThomGame.Analysis.finiteSign_expect_mul
#print axioms ThomGame.Analysis.finiteSignSum_map
#print axioms ThomGame.Analysis.finiteSignSum_sub
#print axioms ThomGame.Analysis.finiteSignSum_norm_sq
#print axioms ThomGame.Analysis.finiteSignSum_expect_norm_sq
#print axioms ThomGame.Analysis.finite_expect_le_sqrt_expect_sq
#print axioms ThomGame.Analysis.sqrt_expect_sq_le_of_pointwise
#print axioms ThomGame.Analysis.matrixOrthogonalSum_projection
#print axioms ThomGame.Analysis.matrixSignSum_selfAdjoint
#print axioms ThomGame.Analysis.matrixSignSum_sq
#print axioms ThomGame.Analysis.matrixSignSum_matrixOpNorm_le_one
#print axioms ThomGame.Analysis.matrixSignSum_expect_hsNorm_sq
#print axioms ThomGame.Analysis.matrixSignSum_commutator
#print axioms ThomGame.Analysis.matrixSignSum_expect_energy
#print axioms ThomGame.Analysis.matrixSignSum_expect_map_energy
#print axioms ThomGame.Analysis.matrixSignSum_expect_defect_sq
#print axioms ThomGame.Analysis.matrixOrthogonalFamily_distance_bound
#print axioms ThomGame.Analysis.matrixOrthogonalFamily_energy_bound
#print axioms ThomGame.Analysis.matrixMarkovOrthogonalFamily_distance_bound
#print axioms ThomGame.Analysis.matrixMarkovOrthogonalFamily_energy_bound
#print axioms ThomGame.Analysis.matrixMarkovOrthogonalFamily_bad_energy_bound
#print axioms ThomGame.Analysis.matrixDistanceBad_family_trace_bound
#print axioms ThomGame.Analysis.matrixEnergyBad_family_trace_bound
#print axioms ThomGame.Analysis.matrixProjection_mul_zero_symm
#print axioms ThomGame.Analysis.matrixOrthogonalFinset_card_le
#print axioms ThomGame.Analysis.exists_matrixMaximalOrthogonalFamily
#print axioms ThomGame.Analysis.normalizedTrace_sum
#print axioms ThomGame.Analysis.matrixOrthogonalSum_complement_orthogonal
#print axioms ThomGame.Analysis.exists_matrixProjection_excluding_two
#print axioms ThomGame.Analysis.badProjection_trace_loss_le
#print axioms ThomGame.Analysis.exists_matrixMarkov_good_projection
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_nonneg
#print axioms ThomGame.Analysis.matrixProjectionImprovement_self
#print axioms ThomGame.Analysis.exists_matrixProjection_improvement_of_not_bad
#print axioms ThomGame.Analysis.exists_matrixMarkov_projection_improvement
#print axioms ThomGame.Analysis.exists_matrixMarkov_projection_improvement_diagonal
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_projection_improvement
#check ThomGame.Analysis.finiteSignSum_expect_norm_sq
#check ThomGame.Analysis.matrixSignSum_matrixOpNorm_le_one
#check ThomGame.Analysis.matrixMarkovOrthogonalFamily_distance_bound
#check ThomGame.Analysis.matrixDistanceBad_family_trace_bound
#check ThomGame.Analysis.matrixEnergyBad_family_trace_bound
#check ThomGame.Analysis.exists_matrixMaximalOrthogonalFamily
#check ThomGame.Analysis.exists_matrixMarkov_good_projection
#check ThomGame.Analysis.MatrixProjectionImprovement
#check ThomGame.Analysis.exists_matrixMarkov_projection_improvement
#check ThomGame.Analysis.exists_matrixUltraproduct_projection_improvement

#print axioms ThomGame.Analysis.rectHSNorm_sq
#print axioms ThomGame.Analysis.rectangular_trace_gram
#print axioms ThomGame.Analysis.rectHSNorm_eq_sqrt_gram
#print axioms ThomGame.Analysis.rectHSNorm_two_unitaries
#print axioms ThomGame.Analysis.rectHSNorm_eq_zero_iff
#print axioms ThomGame.Analysis.matrixIntertwinerBasis_conjugate
#print axioms ThomGame.Analysis.rectHSNorm_diagonal_intertwiner_sq
#print axioms ThomGame.Analysis.matrixIntertwinerBasis_cfc
#print axioms ThomGame.Analysis.rectHSNorm_cfc_intertwiner_sq
#print axioms ThomGame.Analysis.rectHSNorm_intertwiner_spectral_sq
#print axioms ThomGame.Analysis.rectHSNorm_cfc_intertwiner_sq_le
#print axioms ThomGame.Analysis.rectHSNorm_cfc_intertwiner_le_of_spectral_bound
#print axioms ThomGame.Analysis.rectHSNorm_cfc_intertwiner_le_lipschitz
#print axioms ThomGame.Analysis.rectHSNorm_cfc_sub_le
#print axioms ThomGame.Analysis.hsNorm_cfc_sub_le
#print axioms ThomGame.Analysis.rectHSNorm_cfc_abs_sub_le
#print axioms ThomGame.Analysis.matrix_fromBlocks_diagonal_nonneg
#print axioms ThomGame.Analysis.rectHSNorm_fromBlocks_sq
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_isHermitian
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_sq
#print axioms ThomGame.Analysis.rectHSNorm_selfAdjointDilation_sq
#print axioms ThomGame.Analysis.matrixRectAbs_mul_self
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_abs
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_cfc_abs
#print axioms ThomGame.Analysis.rectHSNorm_rectAbs
#print axioms ThomGame.Analysis.rectHSNorm_rectAbs_pair_sub_sq_le
#print axioms ThomGame.Analysis.rectHSNorm_rectAbs_sub_sq_le
#print axioms ThomGame.Analysis.rectHSNorm_rectAbs_sub_le
#print axioms ThomGame.Analysis.hsNorm_cfcAbs_sub_sq_le
#print axioms ThomGame.Analysis.hsNorm_cfcAbs_sub_le
#print axioms ThomGame.Analysis.hsNorm_cfc_commutator_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_cfc_le
#print axioms ThomGame.Analysis.realNormClamp_lipschitz
#print axioms ThomGame.Analysis.hsNorm_normClamp_sub_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_normClamp_le
#print axioms ThomGame.Analysis.hsNorm_cfc_positivePart_sub_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_cfc_positivePart_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_cfc_abs_le
#check ThomGame.Analysis.rectHSNorm_cfc_intertwiner_le_of_spectral_bound
#check ThomGame.Analysis.hsNorm_cfc_sub_le
#check ThomGame.Analysis.matrixSelfAdjointDilation_abs
#check ThomGame.Analysis.rectHSNorm_rectAbs_pair_sub_sq_le
#check ThomGame.Analysis.rectHSNorm_rectAbs_sub_sq_le
#check ThomGame.Analysis.hsNorm_cfcAbs_sub_sq_le
#check ThomGame.Analysis.matrixCoordinateEnergy_cfc_le
#check ThomGame.Analysis.hsNorm_normClamp_sub_le

#print axioms ThomGame.Analysis.matrixCoverageResidual_nonneg
#print axioms ThomGame.Analysis.matrixCoverageResidual_isSelfAdjoint
#print axioms ThomGame.Analysis.matrixCoverageDefect_eq_hsNorm_sq
#print axioms ThomGame.Analysis.matrixCoverageDefect_nonneg
#print axioms ThomGame.Analysis.matrix_sqrt_eq_cfc_real
#print axioms ThomGame.Analysis.matrix_one_le_sqrt_iff
#print axioms ThomGame.Analysis.matrixCoverageResidual_eq_zero_iff
#print axioms ThomGame.Analysis.matrixCoverageDefect_eq_zero_iff
#print axioms ThomGame.Analysis.matrix_sqrt_projection
#print axioms ThomGame.Analysis.matrixCoverageResidual_projection
#print axioms ThomGame.Analysis.matrixCoverageDefect_projection
#print axioms ThomGame.Analysis.matrixFamilyCoverageDefect_nonneg
#print axioms ThomGame.Analysis.matrixFamilyCoverageDefect_eq_zero_iff
#print axioms ThomGame.Analysis.matrixFamilyCoverageDefect_orthogonal
#print axioms ThomGame.Analysis.normalizedTrace_re_mono
#print axioms ThomGame.Analysis.matrix_posPart_eq_cfc
#print axioms ThomGame.Analysis.matrix_mul_spectralCut_zero
#print axioms ThomGame.Analysis.normalizedTrace_mul_le_posPart
#print axioms ThomGame.Analysis.normalizedTrace_posPart_variational
#print axioms ThomGame.Analysis.normalizedTrace_posPart_add_le
#print axioms ThomGame.Analysis.normalizedTrace_posPart_mono
#print axioms ThomGame.Analysis.normalizedTrace_posPart_sum_le
#print axioms ThomGame.Analysis.realCoverageResidual_continuous
#print axioms ThomGame.Analysis.realCoverageResidual_nonneg
#print axioms ThomGame.Analysis.realCoverageResidual_le_one
#print axioms ThomGame.Analysis.realCoverageResidual_sq_le
#print axioms ThomGame.Analysis.matrix_one_sub_posPart_cfc
#print axioms ThomGame.Analysis.matrixCoverageResidual_eq_cfc
#print axioms ThomGame.Analysis.matrixCoverageResidual_le_one
#print axioms ThomGame.Analysis.matrixCoverageResidual_sq_le_posPart
#print axioms ThomGame.Analysis.matrixCoverageDefect_le_posPart_trace
#print axioms ThomGame.Analysis.matrixCoverageDefect_le_one
#print axioms ThomGame.Analysis.matrixFamilyCoverageDefect_comparison
#print axioms ThomGame.Analysis.matrix_positive_shift_eq_cfc
#print axioms ThomGame.Analysis.matrixPositiveResolvent_isSelfAdjoint
#print axioms ThomGame.Analysis.matrixPositiveResolvent_nonneg
#print axioms ThomGame.Analysis.matrixPositiveResolvent_mul_shift
#print axioms ThomGame.Analysis.matrixPositiveResolvent_eq_inverse
#print axioms ThomGame.Analysis.matrixPositiveResolvent_shift_mul
#print axioms ThomGame.Analysis.matrixPositiveResolvent_norm_le
#print axioms ThomGame.Analysis.matrixPositiveResolvent_le_scalar
#print axioms ThomGame.Analysis.matrixPositiveResolvent_difference
#print axioms ThomGame.Analysis.matrixPositiveResolvent_hsNorm_sub_le
#print axioms ThomGame.Analysis.matrixPositiveResolvent_mul_self
#print axioms ThomGame.Analysis.matrixPositiveResolvent_self_mul
#print axioms ThomGame.Analysis.matrixPositiveResolvent_self_mul_nonneg
#print axioms ThomGame.Analysis.matrixPositiveResolvent_self_mul_le_one
#print axioms ThomGame.Analysis.projection_inverse_update_mul
#print axioms ThomGame.Analysis.matrixProjectionResolventCore_nonneg
#print axioms ThomGame.Analysis.matrixPositiveResolvent_projection_update
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_factor
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_nonneg
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_le_resolvent
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_le_one
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_rank_le
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_eq_factor
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_le_gram
#print axioms ThomGame.Analysis.normalizedTrace_mul_re_mono
#print axioms ThomGame.Analysis.matrix_positive_contraction_mul_self_le_one
#print axioms ThomGame.Analysis.matrixPositiveResolvent_self_mul_commute
#print axioms ThomGame.Analysis.matrixPositiveResolvent_weighted_trace
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_weighted_trace_le
#print axioms ThomGame.Analysis.matrixProjectionPartialSum_zero
#print axioms ThomGame.Analysis.matrixProjectionPartialSum_succ
#print axioms ThomGame.Analysis.matrixProjectionPartialSum_nonneg
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_sum
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_nonneg
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_sum_le_one
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_weighted_trace_sum_le
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_coverage_bound
#print axioms ThomGame.Analysis.matrixPositiveResolvent_self_mul_eq_cfc
#print axioms ThomGame.Analysis.matrixPositiveResolvent_projection_missing_le
#print axioms ThomGame.Analysis.real_resolvent_low_cut_bound
#print axioms ThomGame.Analysis.matrixPositiveResolvent_scaled_low_cut_le
#print axioms ThomGame.Analysis.matrixPositiveResolvent_low_cut_trace_le
#print axioms ThomGame.Analysis.matrixResolventFamily_coverage_of_rounding
#check ThomGame.Analysis.matrixFamilyCoverageDefect_eq_zero_iff
#check ThomGame.Analysis.matrixFamilyCoverageDefect_orthogonal
#check ThomGame.Analysis.normalizedTrace_posPart_add_le
#check ThomGame.Analysis.matrixFamilyCoverageDefect_comparison
#check ThomGame.Analysis.matrixPositiveResolvent_eq_inverse
#check ThomGame.Analysis.matrixProjectionResolventDifference_eq_factor
#check ThomGame.Analysis.matrixProjectionResolventDifference_rank_le
#check ThomGame.Analysis.matrixProjectionResolventDifference_weighted_trace_le
#check ThomGame.Analysis.matrixResolventDifferenceFamily_sum
#check ThomGame.Analysis.matrixResolventDifferenceFamily_weighted_trace_sum_le
#check ThomGame.Analysis.matrixResolventFamily_coverage_of_rounding

#print axioms ThomGame.Analysis.matrix_rank_eq_nonzero_eigenvalue_sum
#print axioms ThomGame.Analysis.matrixProjection_eigenvalue_zero_or_one
#print axioms ThomGame.Analysis.matrixProjection_trace_eq_rank
#print axioms ThomGame.Analysis.matrixProjection_rank_trace_mono
#print axioms ThomGame.Analysis.matrix_cfc_trace
#print axioms ThomGame.Analysis.matrix_cfc_rank
#print axioms ThomGame.Analysis.matrix_cfc_rank_le
#print axioms ThomGame.Analysis.matrixSpectralCut_rank_le
#print axioms ThomGame.Analysis.real_spectral_rounding_posPart_le_rank_weight
#print axioms ThomGame.Analysis.matrix_spectral_rounding_posPart_cfc
#print axioms ThomGame.Analysis.matrix_spectral_rounding_posPart_trace_le
#print axioms ThomGame.Analysis.matrix_spectral_rounding_posPart_trace_le_projection
#print axioms ThomGame.Analysis.matrixSpectralCut_le_scaled
#print axioms ThomGame.Analysis.normalizedTrace_real_smul
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_isStarProjection
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_rank_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_rounding_trace_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_rounding_sum_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_weighted_trace_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_weighted_trace_sum_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_rounding_gamma_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_weighted_gamma_le
#print axioms ThomGame.Analysis.matrixResolventSpectralProjection_coverage
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_trace_sum_le_one
#print axioms ThomGame.Analysis.exists_matrixResolventRounding_energy_le
#print axioms ThomGame.Analysis.exists_matrixResolventSpectralRounding
#check ThomGame.Analysis.matrixProjection_trace_eq_rank
#check ThomGame.Analysis.matrix_cfc_rank_le
#check ThomGame.Analysis.matrix_spectral_rounding_posPart_trace_le
#check ThomGame.Analysis.matrixResolventSpectralProjection_rounding_sum_le
#check ThomGame.Analysis.matrixResolventSpectralProjection_weighted_trace_sum_le
#check ThomGame.Analysis.matrixResolventSpectralProjection_coverage
#check ThomGame.Analysis.exists_matrixResolventSpectralRounding

#print axioms ThomGame.Analysis.matrix_inverse_hasDerivAt
#print axioms ThomGame.Analysis.matrixAffineResolvent_eq_positive
#print axioms ThomGame.Analysis.matrixAffineResolvent_hasDerivAt
#print axioms ThomGame.Analysis.matrixAffineResolvent_continuousOn
#print axioms ThomGame.Analysis.normalizedTrace_re_hasDerivAt
#print axioms ThomGame.Analysis.matrixResolventPotential_hasDerivAt
#print axioms ThomGame.Analysis.normalizedTrace_sandwich_gram
#print axioms ThomGame.Analysis.normalizedTrace_inverse_commutator_gram
#print axioms ThomGame.Analysis.matrixResolventPotential_eq_hsNorm_sq
#print axioms ThomGame.Analysis.matrixResolventPotential_nonneg
#print axioms ThomGame.Analysis.matrixResolventPotential_scalar
#print axioms ThomGame.Analysis.matrix_inverse_conjugation_difference
#print axioms ThomGame.Analysis.normalizedTrace_projection_sandwich
#print axioms ThomGame.Analysis.normalizedTrace_involution_commutators
#print axioms ThomGame.Analysis.matrix_sqrt_left_gram
#print axioms ThomGame.Analysis.normalizedTrace_resolvent_dissipation
#print axioms ThomGame.Analysis.matrixResolventPotential_hasDerivAt_dissipation
#print axioms ThomGame.Analysis.abs_normalizedTrace_pairing_re_le
#print axioms ThomGame.Analysis.matrix_commutator_star
#print axioms ThomGame.Analysis.matrix_projection_commutator_offDiagonal
#print axioms ThomGame.Analysis.normalizedTrace_skew_offDiagonal_pairing
#print axioms ThomGame.Analysis.abs_normalizedTrace_commutator_pairing_le
#print axioms ThomGame.Analysis.hsNorm_sqrt_left_sq_lower
#print axioms ThomGame.Analysis.hsNorm_selfAdjoint_involution_mul
#print axioms ThomGame.Analysis.matrixResolvent_dissipation_lower
#print axioms ThomGame.Analysis.resolvent_young_bound
#print axioms ThomGame.Analysis.matrixResolvent_dissipation_bound
#print axioms ThomGame.Analysis.matrixResolventPotential_derivative_bound
#print axioms ThomGame.Analysis.matrixResolventColumnEnergy_nonneg
#print axioms ThomGame.Analysis.matrixResolventColumnEnergy_continuousOn
#print axioms ThomGame.Analysis.matrixResolvent_integrated_step
#print axioms ThomGame.Analysis.matrixResolvent_integrated_partial_sum
#print axioms ThomGame.Analysis.matrixResolvent_integrated_family
#print axioms ThomGame.Analysis.hsNorm_real_smul
#print axioms ThomGame.Analysis.hsNorm_mul_projection_le
#print axioms ThomGame.Analysis.hsNorm_projection_mul_le
#print axioms ThomGame.Analysis.matrixAffineResolvent_initial_identity
#print axioms ThomGame.Analysis.matrix_inverse_update_commutator_column
#print axioms ThomGame.Analysis.matrixResolvent_column_comparison
#print axioms ThomGame.Analysis.matrixResolvent_column_endpoint_bound
#print axioms ThomGame.Analysis.matrixResolvent_endpoint_integral_bound
#print axioms ThomGame.Analysis.resolvent_endpoint_total_bound
#print axioms ThomGame.Analysis.matrixResolvent_selfAdjoint_family_bound
#check ThomGame.Analysis.matrixAffineResolvent_hasDerivAt
#check ThomGame.Analysis.matrixResolventPotential_eq_hsNorm_sq
#check ThomGame.Analysis.matrixResolventPotential_hasDerivAt_dissipation
#check ThomGame.Analysis.abs_normalizedTrace_commutator_pairing_le
#check ThomGame.Analysis.matrixResolventPotential_derivative_bound
#check ThomGame.Analysis.matrixResolvent_integrated_family
#check ThomGame.Analysis.matrixResolvent_column_endpoint_bound
#check ThomGame.Analysis.matrixResolvent_selfAdjoint_family_bound

#print axioms ThomGame.Analysis.rectHSNorm_reindex
#print axioms ThomGame.Analysis.matrixSumReindex_rectHSNorm
#print axioms ThomGame.Analysis.matrixDoubleBlocks_star
#print axioms ThomGame.Analysis.matrixDoubleBlocks_mul
#print axioms ThomGame.Analysis.matrixDoubleBlocks_sub
#print axioms ThomGame.Analysis.matrixDoubleBlocks_one
#print axioms ThomGame.Analysis.matrixDoubleBlocks_hsNorm_sq
#print axioms ThomGame.Analysis.matrixDiagonalDouble_apply
#print axioms ThomGame.Analysis.matrixDiagonalDouble_nonneg
#print axioms ThomGame.Analysis.matrixDiagonalDouble_projection
#print axioms ThomGame.Analysis.matrixDiagonalDouble_resolvent
#print axioms ThomGame.Analysis.matrixDiagonalDouble_partial_sum
#print axioms ThomGame.Analysis.matrixDiagonalDouble_hsNorm_sq
#print axioms ThomGame.Analysis.matrixUnitaryDouble_isSelfAdjoint
#print axioms ThomGame.Analysis.matrixUnitaryDouble_mul_self
#print axioms ThomGame.Analysis.hsNorm_unitary_star_commutator
#print axioms ThomGame.Analysis.matrixUnitaryDouble_commutator
#print axioms ThomGame.Analysis.matrixUnitaryDouble_commutator_column
#print axioms ThomGame.Analysis.matrixUnitaryDouble_commutator_hsNorm_sq
#print axioms ThomGame.Analysis.matrixUnitaryDouble_commutator_column_lower
#print axioms ThomGame.Analysis.matrixResolvent_unitary_family_bound
#print axioms ThomGame.Analysis.matrixProjectionPrepend_partial_sum
#print axioms ThomGame.Analysis.matrixResolvent_unitary_family_bound_initial
#print axioms ThomGame.Analysis.real_inverse_sqrt_lipschitz
#print axioms ThomGame.Analysis.matrixResolventSqrt_eq_cfc
#print axioms ThomGame.Analysis.matrixResolventSqrt_norm_le
#print axioms ThomGame.Analysis.hsNorm_resolventSqrt_commutator_le
#print axioms ThomGame.Analysis.hsNorm_commutator_mul_le
#print axioms ThomGame.Analysis.hsNorm_unitary_commutator_star
#print axioms ThomGame.Analysis.hsNorm_unitary_commutator_gram_le
#print axioms ThomGame.Analysis.matrixProjectionResolventFactor_norm_le
#print axioms ThomGame.Analysis.hsNorm_projection_resolvent_core_commutator_le
#print axioms ThomGame.Analysis.hsNorm_projection_resolvent_sqrt_commutator_le
#print axioms ThomGame.Analysis.resolvent_factor_coeff_bound
#print axioms ThomGame.Analysis.resolvent_factor_square_bound
#print axioms ThomGame.Analysis.hsNorm_projection_resolvent_factor_commutator_le
#print axioms ThomGame.Analysis.hsNorm_projection_resolvent_factor_commutator_sq_le
#print axioms ThomGame.Analysis.hsNorm_projection_resolvent_difference_commutator_sq_le
#print axioms ThomGame.Analysis.resolvent_difference_total_bound
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_commutator_sum_le
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_energy_sum_le
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_energy_fin_sum_le
#print axioms ThomGame.Analysis.resolvent_rounding_small_energy
#print axioms ThomGame.Analysis.matrixResolventDifferenceFamily_energy_gamma_le
#print axioms ThomGame.Analysis.exists_matrixResolventSmallEnergyRounding
#print axioms ThomGame.Analysis.exists_matrixProjectionFamily_small_energy_coverage
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_isStarProjection
#print axioms ThomGame.Analysis.matrix_spectral_complement_le_closedLow
#print axioms ThomGame.Analysis.matrix_spectral_complement_trace_le_closedLow
#print axioms ThomGame.Analysis.exists_matrixProjectionFamily_ALT_lemma3_3
#print axioms ThomGame.Analysis.matrixExtendFiniteFamily_apply
#print axioms ThomGame.Analysis.matrixExtendFiniteFamily_projection
#print axioms ThomGame.Analysis.matrixExtendFiniteFamily_sum
#print axioms ThomGame.Analysis.matrixExtendFiniteFamily_total
#print axioms ThomGame.Analysis.matrixResolvent_unitary_finite_family_bound
#print axioms ThomGame.Analysis.exists_matrixFiniteProjectionFamily_ALT_lemma3_3
#check ThomGame.Analysis.matrixDoubleBlocks_hsNorm_sq
#check ThomGame.Analysis.matrixDiagonalDouble_resolvent
#check ThomGame.Analysis.matrixUnitaryDouble_commutator_column_lower
#check ThomGame.Analysis.matrixResolvent_unitary_family_bound
#check ThomGame.Analysis.matrixResolvent_unitary_family_bound_initial
#check ThomGame.Analysis.hsNorm_resolventSqrt_commutator_le
#check ThomGame.Analysis.matrixProjectionResolventFactor_norm_le
#check ThomGame.Analysis.hsNorm_projection_resolvent_difference_commutator_sq_le
#check ThomGame.Analysis.matrixResolventDifferenceFamily_energy_sum_le
#check ThomGame.Analysis.exists_matrixResolventSmallEnergyRounding
#check ThomGame.Analysis.exists_matrixProjectionFamily_ALT_lemma3_3
#check ThomGame.Analysis.matrixResolvent_unitary_finite_family_bound
#check ThomGame.Analysis.exists_matrixFiniteProjectionFamily_ALT_lemma3_3

#print axioms ThomGame.Analysis.matrixRealSupport_isStarProjection
#print axioms ThomGame.Analysis.matrixRealInv_mul
#print axioms ThomGame.Analysis.matrix_mul_absSupport
#print axioms ThomGame.Analysis.matrixRectPolar_mul_abs
#print axioms ThomGame.Analysis.matrixRectPolar_initial
#print axioms ThomGame.Analysis.matrixRectPolar_partial_isometry
#print axioms ThomGame.Analysis.matrixRectPolar_final_projection
#print axioms ThomGame.Analysis.matrix_cfc_intertwine
#print axioms ThomGame.Analysis.matrix_cfc_blockDiagonal
#print axioms ThomGame.Analysis.matrixRectAbs_intertwine
#print axioms ThomGame.Analysis.matrixRectPolar_conjTranspose
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_sign
#print axioms ThomGame.Analysis.realClippedSign_bound
#print axioms ThomGame.Analysis.realClippedSign_eq_sign
#print axioms ThomGame.Analysis.rectHSNorm_sign_sub_le
#print axioms ThomGame.Analysis.rectHSNorm_polar_sub_le
#print axioms ThomGame.Analysis.matrixRectPolar_final
#print axioms ThomGame.Analysis.matrixRectPolar_abs_conjugate
#print axioms ThomGame.Analysis.matrixRectPolar_rank
#print axioms ThomGame.Analysis.matrixRectPolar_initial_rank
#print axioms ThomGame.Analysis.matrixRectPolar_final_rank
#print axioms ThomGame.Analysis.matrixRectAbs_support_lower_adjoint
#print axioms ThomGame.Analysis.matrixRealSupport_lower_iff
#print axioms ThomGame.Analysis.matrixHasPolarGap_of_support_lower
#print axioms ThomGame.Analysis.matrixHasPolarGap_of_singularValues
#print axioms ThomGame.Analysis.rectHSNorm_polar_sub_le_of_singularValues
#print axioms ThomGame.Analysis.matrixRectPolar_two_unitaries
#print axioms ThomGame.Analysis.matrixRectAbs_spectrum_unitary_right
#print axioms ThomGame.Analysis.rectHSNorm_polar_intertwiner_le
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_eq_coordinate
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_le_hsNorm_sq
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_add_le
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_perturb_le
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_polar_le
#print axioms ThomGame.Analysis.matrix_absSupport_mul_eq_zero
#print axioms ThomGame.Analysis.matrix_absSupport_of_left_inverse
#print axioms ThomGame.Analysis.matrixRectPolar_of_initial_projection
#print axioms ThomGame.Analysis.matrixRectPolar_initial_partial_isometry_left_inverse
#print axioms ThomGame.Analysis.rectHSNorm_mul_le_left
#print axioms ThomGame.Analysis.rectHSNorm_mul_le_right
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_mul_le
#print axioms ThomGame.Analysis.matrixRectAbs_left_multiplier_lower
#print axioms ThomGame.Analysis.matrixRectAbs_left_multiplier_singularValues
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_polar_mul_le
#print axioms ThomGame.Analysis.matrixRealExp_eq_exp
#print axioms ThomGame.Analysis.matrixRealExp_inverse
#print axioms ThomGame.Analysis.matrixRealExp_norm_le
#print axioms ThomGame.Analysis.matrixRealExp_coercive
#print axioms ThomGame.Analysis.matrixExponentialPolarTilt_initial
#print axioms ThomGame.Analysis.matrixExponentialPolarTilt_partial_isometry
#print axioms ThomGame.Analysis.matrixExponentialPolarTilt_energy_le
#check ThomGame.Analysis.matrixRectPolar_initial
#check ThomGame.Analysis.matrixSelfAdjointDilation_sign
#check ThomGame.Analysis.rectHSNorm_polar_sub_le_of_singularValues
#check ThomGame.Analysis.rectHSNorm_polar_intertwiner_le
#check ThomGame.Analysis.matrixIntertwiningEnergy_perturb_le
#check ThomGame.Analysis.matrixRectPolar_initial_partial_isometry_left_inverse
#check ThomGame.Analysis.matrixRealExp_eq_exp
#check ThomGame.Analysis.matrixExponentialPolarTilt_initial
#check ThomGame.Analysis.matrixExponentialPolarTilt_energy_le

#print axioms ThomGame.Analysis.matrix_support_fill_inverse
#print axioms ThomGame.Analysis.matrixFilledGram_isUnit
#print axioms ThomGame.Analysis.matrixFilledGram_inverse
#print axioms ThomGame.Analysis.matrixFilledGram_range_formula
#print axioms ThomGame.Analysis.rectangular_mul_hasDerivAt
#print axioms ThomGame.Analysis.rectangular_adjoint_hasDerivAt
#print axioms ThomGame.Analysis.squareMatrix_inverse_hasDerivAt
#print axioms ThomGame.Analysis.matrixRangeProjection_fixed_formula
#print axioms ThomGame.Analysis.matrixRangeProjection_hasDerivAt
#print axioms ThomGame.Analysis.matrixTraceReal_gram
#print axioms ThomGame.Analysis.matrixTraceReal_nonneg
#print axioms ThomGame.Analysis.matrixTraceReal_hasDerivAt
#print axioms ThomGame.Analysis.matrixRealExp_affine_factor
#print axioms ThomGame.Analysis.matrixRealExp_affine_hasDerivAt
#print axioms ThomGame.Analysis.matrixExponentialRange_hasDerivAt
#print axioms ThomGame.Analysis.matrixTraceReal_projection_sandwich
#print axioms ThomGame.Analysis.matrixTraceReal_compression_square
#print axioms ThomGame.Analysis.matrixProjectionMixing_eq_source
#print axioms ThomGame.Analysis.matrixProjectionMixing_eq_hsNorm_sq
#print axioms ThomGame.Analysis.matrixProjectionMixing_nonneg
#print axioms ThomGame.Analysis.matrixProjectionMixing_le_trace
#print axioms ThomGame.Analysis.matrixTraceReal_projection_tangent
#print axioms ThomGame.Analysis.uniform_interval_integration_by_parts
#print axioms ThomGame.Analysis.matrixExponentialRange_trace_hasDerivAt
#print axioms ThomGame.Analysis.matrixExponentialMixing_interval_identity
#print axioms ThomGame.Analysis.matrixBlockPinch_nonneg
#print axioms ThomGame.Analysis.matrixBlockPinch_one
#print axioms ThomGame.Analysis.matrixBlockPinch_trace
#print axioms ThomGame.Analysis.matrixBlockPinch_commute
#print axioms ThomGame.Analysis.matrixBlockPinch_idempotent
#print axioms ThomGame.Analysis.matrixBlockPinch_trace_pairing
#print axioms ThomGame.Analysis.matrixBlockPinch_projection_bounds
#print axioms ThomGame.Analysis.rectHSNorm_pinching_defect_eq_trace
#print axioms ThomGame.Analysis.rectHSNorm_pinching_defect_eq_mixing_sum
#print axioms ThomGame.Analysis.matrixProjectionParameter_norm_le_one
#print axioms ThomGame.Analysis.matrixProjectionParameter_update
#print axioms ThomGame.Analysis.matrixPartitionRange_coordinate_derivative
#print axioms ThomGame.Analysis.matrixPartitionRange_trace_derivative
#print axioms ThomGame.Analysis.matrixPartitionRange_coordinate_interval
#print axioms ThomGame.Analysis.matrixPartitionRange_defect
#print axioms ThomGame.Analysis.matrixPartitionPolarTilt_energy
#check ThomGame.Analysis.matrixFilledGram_range_formula
#check ThomGame.Analysis.matrixRangeProjection_hasDerivAt
#check ThomGame.Analysis.matrixExponentialRange_hasDerivAt
#check ThomGame.Analysis.matrixProjectionMixing_eq_source
#check ThomGame.Analysis.matrixProjectionMixing_eq_hsNorm_sq
#check ThomGame.Analysis.matrixPartitionRange_coordinate_derivative
#check ThomGame.Analysis.matrixPartitionRange_trace_derivative
#check ThomGame.Analysis.matrixPartitionRange_coordinate_interval
#check ThomGame.Analysis.matrixPartitionRange_defect
#check ThomGame.Analysis.matrixPartitionPolarTilt_energy

#print axioms ThomGame.Analysis.squareMatrix_inverse_continuous
#print axioms ThomGame.Analysis.matrixRangeProjection_continuous_of_fixed_support
#print axioms ThomGame.Analysis.matrixPartitionRange_continuous
#print axioms ThomGame.Analysis.uniformIntervalMeasure_probability
#print axioms ThomGame.Analysis.uniformCubeMeasure_probability
#print axioms ThomGame.Analysis.uniformCubeMeasure_ae
#print axioms ThomGame.Analysis.uniformCube_integrable
#print axioms ThomGame.Analysis.measurePreserving_product_update
#print axioms ThomGame.Analysis.integral_product_update
#print axioms ThomGame.Analysis.matrixPartitionRange_coordinate_expectation
#print axioms ThomGame.Analysis.matrixPartitionRange_joint_expectation
#print axioms ThomGame.Analysis.matrixPartitionRange_trace
#print axioms ThomGame.Analysis.matrixPartitionRange_weighted_expectation_le_one
#print axioms ThomGame.Analysis.uniformBoundaryWeight_integral
#print axioms ThomGame.Analysis.uniformCube_boundary_integral
#print axioms ThomGame.Analysis.uniformBoundary_weighted_bound
#print axioms ThomGame.Analysis.uniformCube_exists_le_integral
#print axioms ThomGame.Analysis.uniformCube_mixing_expectation_le
#print axioms ThomGame.Analysis.matrixPartition_trace_sum_le_three
#print axioms ThomGame.Analysis.matrixPartitionRange_defect_expectation_le
#print axioms ThomGame.Analysis.exists_matrixPartitionRange_small_defect
#print axioms ThomGame.Analysis.exists_matrixPartitionPolarTilt_good_parameter
#check ThomGame.Analysis.matrixPartitionRange_joint_expectation
#check ThomGame.Analysis.matrixPartitionRange_weighted_expectation_le_one
#check ThomGame.Analysis.uniformCube_mixing_expectation_le
#check ThomGame.Analysis.matrixPartitionRange_defect_expectation_le
#check ThomGame.Analysis.exists_matrixPartitionRange_small_defect
#check ThomGame.Analysis.exists_matrixPartitionPolarTilt_good_parameter

#print axioms ThomGame.Analysis.matrixHalfProjection_isStarProjection
#print axioms ThomGame.Analysis.matrixHalfProjection_eq_closed_interval
#print axioms ThomGame.Analysis.matrixHalfProjection_order_bounds
#print axioms ThomGame.Analysis.matrixHalfProjection_pinching_commute
#print axioms ThomGame.Analysis.matrixHalfProjection_pinching_distance_le
#print axioms ThomGame.Analysis.matrixHalfProjection_pinching_trace_error_le
#print axioms ThomGame.Analysis.matrixTraceReal_projection_rank
#print axioms ThomGame.Analysis.matrixBasisProjection_rank
#print axioms ThomGame.Analysis.exists_matrixSubprojection_rank
#print axioms ThomGame.Analysis.finite_rank_allocation
#print axioms ThomGame.Analysis.matrixProjection_sum_rank
#print axioms ThomGame.Analysis.matrixProjection_rank_sub_add
#print axioms ThomGame.Analysis.exists_matrixBlockSubprojection_rank
#print axioms ThomGame.Analysis.exists_matrixBlockProjection_rank
#print axioms ThomGame.Analysis.rectHSNorm_projection_nested_correction
#print axioms ThomGame.Analysis.exists_matrixPinching_rank_corrected
#print axioms ThomGame.Analysis.matrixProjectionFrame_initial
#print axioms ThomGame.Analysis.matrixProjectionFrame_final
#print axioms ThomGame.Analysis.exists_matrixPartialIsometry_of_rank_eq
#print axioms ThomGame.Analysis.matrixRectPolar_initial_le
#print axioms ThomGame.Analysis.matrixRectPolar_final_le
#print axioms ThomGame.Analysis.exists_matrixPolar_completion
#print axioms ThomGame.Analysis.matrixRectAbs_ge_gram_of_gram_le_one
#print axioms ThomGame.Analysis.exists_matrixPartialIsometry_close_to_projection
#print axioms ThomGame.Analysis.exists_matrixPartialIsometry_block_correction
#print axioms ThomGame.Analysis.exists_matrixPartialIsometry_ALT_lemma3_4
#check ThomGame.Analysis.matrixHalfProjection_eq_closed_interval
#check ThomGame.Analysis.exists_matrixBlockProjection_rank
#check ThomGame.Analysis.exists_matrixPinching_rank_corrected
#check ThomGame.Analysis.exists_matrixPolar_completion
#check ThomGame.Analysis.exists_matrixPartialIsometry_close_to_projection
#check ThomGame.Analysis.exists_matrixPartialIsometry_block_correction
#check ThomGame.Analysis.exists_matrixPartialIsometry_ALT_lemma3_4

#print axioms ThomGame.Analysis.exists_matrixCompressionPolar
#print axioms ThomGame.Analysis.rectHSNorm_frame_mul
#print axioms ThomGame.Analysis.exists_matrixCornerUnitary
#print axioms ThomGame.Analysis.exists_matrixFrameCompressionUnitary
#print axioms ThomGame.Analysis.matrixRectClamp_eq_polar_min
#print axioms ThomGame.Analysis.matrixRectClamp_gram
#print axioms ThomGame.Analysis.matrixRectClamp_abs
#print axioms ThomGame.Analysis.matrixRectClamp_abs_le_one
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_clamp
#print axioms ThomGame.Analysis.matrixRectClamp_gram_le_one
#print axioms ThomGame.Analysis.matrixRectClamp_two_unitaries
#print axioms ThomGame.Analysis.rectHSNorm_clamp_sub_le
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_clamp_le
#print axioms ThomGame.Analysis.matrixBlockColumn_gram
#print axioms ThomGame.Analysis.rectHSNorm_blockColumn_sq
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_blockColumn
#print axioms ThomGame.Analysis.matrixBlockLabel_projection
#print axioms ThomGame.Analysis.matrixBlockLabel_orthogonal
#print axioms ThomGame.Analysis.matrixBlockLabel_sum
#print axioms ThomGame.Analysis.matrixBlockLabel_commute
#print axioms ThomGame.Analysis.matrixProjectionColumn_gram
#print axioms ThomGame.Analysis.matrixProjectionSumIndex_card_le_three
#print axioms ThomGame.Analysis.matrixProjectionRangeUnitary_errors
#print axioms ThomGame.Analysis.matrixProjectionBlockUnitary_commute
#print axioms ThomGame.Analysis.matrixProjectionColumn_energy_le
#print axioms ThomGame.Analysis.matrixRectClamp_residual
#print axioms ThomGame.Analysis.matrixClippedProjectionColumn_defect
#print axioms ThomGame.Analysis.matrixClippedProjectionColumn_ALT_setup
#print axioms ThomGame.Analysis.matrixThresholdPolar_initial
#print axioms ThomGame.Analysis.matrixThresholdPolar_partialIsometry
#print axioms ThomGame.Analysis.matrixThresholdPolar_initial_closed_interval
#print axioms ThomGame.Analysis.matrixUpperSpectralProjection_complement_le
#print axioms ThomGame.Analysis.matrixThresholdPolar_lost_trace_le
#print axioms ThomGame.Analysis.matrixThresholdPolar_clippedColumn_coverage
#check ThomGame.Analysis.exists_matrixCompressionPolar
#check ThomGame.Analysis.exists_matrixFrameCompressionUnitary
#check ThomGame.Analysis.matrixRectClamp_abs
#check ThomGame.Analysis.rectHSNorm_clamp_sub_le
#check ThomGame.Analysis.matrixIntertwiningEnergy_clamp_le
#check ThomGame.Analysis.matrixClippedProjectionColumn_ALT_setup
#check ThomGame.Analysis.matrixThresholdPolar_clippedColumn_coverage

#print axioms ThomGame.Analysis.signedSpectralStep_sq_sub_intervalIntegrable
#print axioms ThomGame.Analysis.signedSpectralStep_eq_parts
#print axioms ThomGame.Analysis.signedSpectralStep_sq_sub_intervalIntegral_le
#print axioms ThomGame.Analysis.weighted_signedSpectralStep_coarea
#print axioms ThomGame.Analysis.matrixThresholdPolar_conjTranspose
#print axioms ThomGame.Analysis.matrixSelfAdjointDilation_thresholdPolar
#print axioms ThomGame.Analysis.matrixThresholdPolar_unitary_left
#print axioms ThomGame.Analysis.matrixThresholdPolar_unitary_right
#print axioms ThomGame.Analysis.rectHSNorm_signedSpectral_intertwiner_coarea
#print axioms ThomGame.Analysis.rectHSNorm_thresholdPolar_sub_intervalIntegrable
#print axioms ThomGame.Analysis.rectHSNorm_thresholdPolar_sub_coarea
#print axioms ThomGame.Analysis.rectHSNorm_thresholdPolar_intertwiner_coarea
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_threshold_intervalIntegrable
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_firstMoment_le
#print axioms ThomGame.Analysis.matrixThresholdPolar_energy_coarea
#print axioms ThomGame.Analysis.matrixThresholdPolar_ALT_3_13
#print axioms ThomGame.Analysis.exists_matrixThresholdPolar_energy_le
#print axioms ThomGame.Analysis.exists_matrixClippedColumn_good_threshold
#print axioms ThomGame.Analysis.exists_matrixColumn_block_partialIsometry
#print axioms ThomGame.Analysis.rectHSNorm_mul_sq_le_of_final_le_one
#print axioms ThomGame.Analysis.rectHSNorm_mul_sq_le_of_partialIsometry
#print axioms ThomGame.Analysis.matrixPartialIsometry_pullback_mul
#print axioms ThomGame.Analysis.matrixPartialIsometry_pullback_projection
#print axioms ThomGame.Analysis.matrixBlockComponent_initial
#print axioms ThomGame.Analysis.matrixBlockComponent_initial_projection
#print axioms ThomGame.Analysis.matrixBlockComponent_initial_orthogonal
#print axioms ThomGame.Analysis.matrixBlockComponent_initial_sum
#print axioms ThomGame.Analysis.matrixBlockComponent_energy
#print axioms ThomGame.Analysis.matrixProjectionPiece_partialIsometry
#print axioms ThomGame.Analysis.matrixProjectionPiece_final_le
#print axioms ThomGame.Analysis.matrixProjectionPiece_orthogonal
#print axioms ThomGame.Analysis.matrixProjectionPiece_initial_sum
#print axioms ThomGame.Analysis.matrixProjectionPiece_commutator_sq_le
#print axioms ThomGame.Analysis.matrixProjectionPiece_energy_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_partialIsometry_initial_le
#print axioms ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_3_14
#check ThomGame.Analysis.signedSpectralStep_sq_sub_intervalIntegral_le
#check ThomGame.Analysis.matrixThresholdPolar_ALT_3_13
#check ThomGame.Analysis.exists_matrixClippedColumn_good_threshold
#check ThomGame.Analysis.exists_matrixColumn_block_partialIsometry
#check ThomGame.Analysis.matrixProjectionPiece_energy_le
#check ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_3_14

#print axioms ThomGame.Analysis.alt_exp_neg_two_le_inv_sqrt
#print axioms ThomGame.Analysis.alt_exponential_energy_bound
#print axioms ThomGame.Analysis.alt_logarithmic_parameters
#print axioms ThomGame.Analysis.exists_matrixOrthogonalFamily_exponential
#print axioms ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_proposition3_5_pos
#print axioms ThomGame.Analysis.isClosed_matrixStarProjection
#print axioms ThomGame.Analysis.matrixOrthogonalFamilySpace_isClosed
#print axioms ThomGame.Analysis.matrixOrthogonalFamilySpace_nonempty
#print axioms ThomGame.Analysis.matrixOrthogonalFamilySpace_isCompact
#print axioms ThomGame.Analysis.matrixOrthogonalFamilySpace_final_le
#print axioms ThomGame.Analysis.matrixOrthogonalFamilyDefect_nonneg
#print axioms ThomGame.Analysis.matrixOrthogonalFamilyDefect_continuous
#print axioms ThomGame.Analysis.exists_matrixOrthogonalFamilyDefect_minimizer
#print axioms ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_proposition3_5_zero
#print axioms ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_proposition3_5
#print axioms ThomGame.Analysis.alt_inverse_four_large
#print axioms ThomGame.Analysis.alt_inverse_four_sqrt_scale
#print axioms ThomGame.Analysis.alt_correction_parameters
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_mono
#print axioms ThomGame.Analysis.matrixSubprojection_rank_le
#print axioms ThomGame.Analysis.matrixPartialIsometry_initial_rank_le
#print axioms ThomGame.Analysis.exists_matrixOrthogonalCorrection_ALT_proposition3_6
#check ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_proposition3_5_pos
#check ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_proposition3_5_zero
#check ThomGame.Analysis.exists_matrixOrthogonalFamily_ALT_proposition3_5
#check ThomGame.Analysis.exists_matrixOrthogonalCorrection_ALT_proposition3_6

#print axioms ThomGame.Analysis.matrixRectAbs_le_one_of_gram_le_one
#print axioms ThomGame.Analysis.exists_matrixContraction_unitary_pair
#print axioms ThomGame.Analysis.matrixFrameLift_mul
#print axioms ThomGame.Analysis.matrixFrameLift_star
#print axioms ThomGame.Analysis.matrixFrameLift_add
#print axioms ThomGame.Analysis.matrixFrameLift_sub
#print axioms ThomGame.Analysis.matrixFrameLift_smul
#print axioms ThomGame.Analysis.matrixFrameLift_one
#print axioms ThomGame.Analysis.matrixFrameLift_trace
#print axioms ThomGame.Analysis.matrixFrameLift_hsNorm
#print axioms ThomGame.Analysis.matrixFrameLift_compression
#print axioms ThomGame.Analysis.matrixFrameCompression_gram_le_one
#print axioms ThomGame.Analysis.exists_matrixCorner_unitary_pair
#print axioms ThomGame.Analysis.matrix_sum_gram_of_orthogonal
#print axioms ThomGame.Analysis.rectHSNorm_orthogonal_sum_sq
#print axioms ThomGame.Analysis.matrixCorner_gram_support
#print axioms ThomGame.Analysis.matrixCorner_cross_mul
#print axioms ThomGame.Analysis.matrixCorner_sum_block_left
#print axioms ThomGame.Analysis.matrixCorner_sum_block_right
#print axioms ThomGame.Analysis.matrixCorner_sum_gram
#print axioms ThomGame.Analysis.matrixCorner_sum_mem_unitary
#print axioms ThomGame.Analysis.matrixBlockPinch_conjTranspose
#print axioms ThomGame.Analysis.matrixBlockPinch_gram_trace
#print axioms ThomGame.Analysis.rectHSNorm_pinching_defect_gram
#print axioms ThomGame.Analysis.rectHSNorm_pinching_pythagoras
#print axioms ThomGame.Analysis.rectHSNorm_corner_sum_sq
#print axioms ThomGame.Analysis.matrixBlockPinch_corner_sum
#print axioms ThomGame.Analysis.rectHSNorm_corner_correction_pythagoras
#print axioms ThomGame.Analysis.matrixUnitary_projection_gram
#print axioms ThomGame.Analysis.matrixUnitary_compression_gram_le
#print axioms ThomGame.Analysis.rectHSNorm_unitary_projection_commutator_sq
#print axioms ThomGame.Analysis.rectHSNorm_unitary_bad_corner_le
#print axioms ThomGame.Analysis.rectHSNorm_unitary_pinching_defect_sum
#print axioms ThomGame.Analysis.rectHSNorm_unitary_pinching_commutator_sum
#print axioms ThomGame.Analysis.rectHSNorm_unitary_partition_correction_le
#print axioms ThomGame.Analysis.exists_matrixPartition_unitary_pair
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_partition_identity
#print axioms ThomGame.Analysis.exists_matrixPartition_unitary_tuple
#print axioms ThomGame.Analysis.matrixCompressedCoordinateEnergy_nonneg
#print axioms ThomGame.Analysis.hsNorm_compressed_commutator_le_pair
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_append
#print axioms ThomGame.Analysis.matrixCompressedCoordinateEnergy_le_doubled
#print axioms ThomGame.Analysis.exists_matrixPartition_doubled_correction
#check ThomGame.Analysis.exists_matrixContraction_unitary_pair
#check ThomGame.Analysis.exists_matrixCorner_unitary_pair
#check ThomGame.Analysis.rectHSNorm_corner_correction_pythagoras
#check ThomGame.Analysis.exists_matrixPartition_unitary_tuple
#check ThomGame.Analysis.matrixCompressedCoordinateEnergy_le_doubled
#check ThomGame.Analysis.exists_matrixPartition_doubled_correction

#print axioms ThomGame.Analysis.rectHSNorm_sub_orthogonal_sq
#print axioms ThomGame.Analysis.rectHSNorm_add_orthogonal_sq
#print axioms ThomGame.Analysis.rectHSNorm_projection_mul_sq_le
#print axioms ThomGame.Analysis.rectHSNorm_mul_projection_sq_le
#print axioms ThomGame.Analysis.matrixProjection_opposite_cut_orthogonal
#print axioms ThomGame.Analysis.rectHSNorm_projection_commutator_cut
#print axioms ThomGame.Analysis.rectHSNorm_compressed_commutator_cut
#print axioms ThomGame.Analysis.rectHSNorm_add_orthogonal_right_sq
#print axioms ThomGame.Analysis.rectHSNorm_projection_deletion_commutator_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_projection_deletion_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_eq_zero_of_reducing
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_reducing_sub
#print axioms ThomGame.Analysis.matrixTraceReal_projection_eq_zero_iff
#print axioms ThomGame.Analysis.matrixTraceReal_projection_pos
#print axioms ThomGame.Analysis.matrixProjection_rank_pos
#print axioms ThomGame.Analysis.matrixProjection_trace_le_half_iff
#print axioms ThomGame.Analysis.matrixProjection_rank_sub_lt
#print axioms ThomGame.Analysis.matrixProjection_pruning_no_crossing
#print axioms ThomGame.Analysis.matrixProjection_pruning_delete
#print axioms ThomGame.Analysis.exists_matrixPrunedProjection
#print axioms ThomGame.Analysis.exists_matrixPrunedOrDiscardedProjection
#print axioms ThomGame.Analysis.matrixProjectionCompletion_none
#print axioms ThomGame.Analysis.matrixProjectionCompletion_some
#print axioms ThomGame.Analysis.matrixProjectionCompletion_isStarProjection
#print axioms ThomGame.Analysis.matrixProjectionCompletion_orthogonal
#print axioms ThomGame.Analysis.matrixProjectionCompletion_sum
#print axioms ThomGame.Analysis.matrixProjection_reducing_commutator_left
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_reducing_sum
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_reducing_complement
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_reducing_completion
#print axioms ThomGame.Analysis.exists_matrixPrunedFamily
#print axioms ThomGame.Analysis.exists_matrixPrunedDoubledExpansion
#check ThomGame.Analysis.matrixCoordinateEnergy_projection_deletion_le
#check ThomGame.Analysis.exists_matrixPrunedProjection
#check ThomGame.Analysis.exists_matrixPrunedFamily
#check ThomGame.Analysis.exists_matrixPrunedDoubledExpansion

#print axioms ThomGame.Analysis.positiveSpectralStep_of_pos
#print axioms ThomGame.Analysis.positiveSpectralStep_of_nonpos
#print axioms ThomGame.Analysis.positiveSpectralStep_nonneg
#print axioms ThomGame.Analysis.positiveSpectralStep_integrable
#print axioms ThomGame.Analysis.positiveSpectralStep_integral
#print axioms ThomGame.Analysis.positiveSpectralStep_sub
#print axioms ThomGame.Analysis.positiveSpectralStep_sub_sq_integrable
#print axioms ThomGame.Analysis.positiveSpectralStep_sub_sq_integral
#print axioms ThomGame.Analysis.finiteWeightedEnergy_nonneg
#print axioms ThomGame.Analysis.finiteSquareVariation_nonneg
#print axioms ThomGame.Analysis.weighted_product_abs_sum_sq_le
#print axioms ThomGame.Analysis.finiteWeightedEnergy_sum_sq_le
#print axioms ThomGame.Analysis.finiteSquareVariation_sq_le
#print axioms ThomGame.Analysis.finiteWeightedEnergy_positive_levels_integrable
#print axioms ThomGame.Analysis.finiteWeightedEnergy_positive_levels_integral
#print axioms ThomGame.Analysis.finiteSquareVariation_lower_of_levels
#print axioms ThomGame.Analysis.finiteWeightedEnergy_cheeger_of_square_levels
#print axioms ThomGame.Analysis.exists_finite_median
#print axioms ThomGame.Analysis.finiteCutVector_sum
#print axioms ThomGame.Analysis.spectralStep_eq_finiteCutVector
#print axioms ThomGame.Analysis.finiteWeightedEnergy_cheeger_half_support
#print axioms ThomGame.Analysis.real_pos_neg_difference_sq_le
#print axioms ThomGame.Analysis.real_pos_neg_sq
#print axioms ThomGame.Analysis.finiteWeightedEnergy_pos_neg_le
#print axioms ThomGame.Analysis.finite_sum_sub_mean
#print axioms ThomGame.Analysis.finite_sum_sq_sub_mean_le
#print axioms ThomGame.Analysis.finiteWeightedEnergy_cheeger
#print axioms ThomGame.Analysis.hsNorm_diagonal_real_sq
#print axioms ThomGame.Analysis.hsNorm_selfAdjoint_center_spectral
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_conjugate_diagonal
#print axioms ThomGame.Analysis.matrixBasisProjection_eq_cut_diagonal
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_cheeger_selfAdjoint
#print axioms ThomGame.Analysis.normalizedTrace_selfAdjoint_real
#print axioms ThomGame.Analysis.matrix_selfAdjoint_center
#print axioms ThomGame.Analysis.hsNorm_selfAdjoint_add_I_smul_sq
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_selfAdjoint_add_I_smul
#print axioms ThomGame.Analysis.hsNorm_center_selfAdjoint_add_I_smul_sq
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_cheeger
#print axioms ThomGame.Analysis.matrixFrameLift_support
#print axioms ThomGame.Analysis.matrixFrameLift_isStarProjection
#print axioms ThomGame.Analysis.matrixFrameLift_projection_le
#print axioms ThomGame.Analysis.matrixFrameLift_projection_rank
#print axioms ThomGame.Analysis.exists_matrixFrameReducingUnitary
#print axioms ThomGame.Analysis.matrixFrameLift_reducing_commutator
#print axioms ThomGame.Analysis.hsNorm_frameLift_sq
#print axioms ThomGame.Analysis.matrixTraceReal_frameLift_scale
#print axioms ThomGame.Analysis.normalizedTrace_frameLift_scale
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_frameLift
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_corner_cheeger
#print axioms ThomGame.Analysis.exists_matrixPartition_ALT_lemma4_2
#check ThomGame.Analysis.finiteWeightedEnergy_cheeger
#check ThomGame.Analysis.matrixCoordinateEnergy_cheeger_selfAdjoint
#check ThomGame.Analysis.matrixCoordinateEnergy_cheeger
#check ThomGame.Analysis.matrixCoordinateEnergy_frameLift
#check ThomGame.Analysis.matrixCoordinateEnergy_corner_cheeger
#check ThomGame.Analysis.exists_matrixPartition_ALT_lemma4_2

#print axioms ThomGame.Analysis.matrixRectPolar_initial_of_gram_lower
#print axioms ThomGame.Analysis.matrixProjection_gram_lower_of_leakage
#print axioms ThomGame.Analysis.matrixProjectionPolar_initial
#print axioms ThomGame.Analysis.matrixProjectionPolar_final_le
#print axioms ThomGame.Analysis.matrixRectAbs_lower_of_gram_lower
#print axioms ThomGame.Analysis.matrixProjectionPolar_abs_lower
#print axioms ThomGame.Analysis.matrixProjectionPolar_compression
#print axioms ThomGame.Analysis.matrix_supported_square_lower
#print axioms ThomGame.Analysis.matrixPartialIsometry_transport_projection
#print axioms ThomGame.Analysis.matrixProjection_conjugate_le_gram
#print axioms ThomGame.Analysis.matrixTraceReal_partialIsometry_transport
#print axioms ThomGame.Analysis.matrixPartialIsometry_transport_rank
#print axioms ThomGame.Analysis.rectHSNorm_partialIsometry_transport_sq_le
#print axioms ThomGame.Analysis.rectHSNorm_projectionPolar_transport_sq_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_projectionPolar_transport_le
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_compression_le
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_leakage
#print axioms ThomGame.Analysis.matrixALT_lowSpectral_polar_transport
#print axioms ThomGame.Analysis.matrixPositiveResolvent_ge_scalar
#print axioms ThomGame.Analysis.matrixALTSelection_inverse
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_eq_resolvent
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_nonneg
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_le_one
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_increment
#print axioms ThomGame.Analysis.matrixProjectionResolventDifference_quarter_ge_gram
#print axioms ThomGame.Analysis.matrixPositiveResolvent_square_ge_lowCut
#print axioms ThomGame.Analysis.matrixTraceReal_projection_mul_mono
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_increment_ge_lowCut
#print axioms ThomGame.Analysis.alt_selection_coefficient
#print axioms ThomGame.Analysis.alt_selection_coefficient_ge
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_increment_ge_source
#print axioms ThomGame.Analysis.matrixALTSelectionPotential_increment_ge_trace
#print axioms ThomGame.Analysis.matrixPartialIsometry_transport_inverse
#print axioms ThomGame.Analysis.rectHSNorm_ALT_three_point_sq_le
#print axioms ThomGame.Analysis.matrixTraceReal_low_overlap_of_distance
#print axioms ThomGame.Analysis.matrixALTSelection_correction_overlap
#print axioms ThomGame.Analysis.matrixALTSelection_corrected_increment
#print axioms ThomGame.Analysis.exists_finite_terminal_path
#print axioms ThomGame.Analysis.exists_matrixALTSelection_minimal
#print axioms ThomGame.Analysis.matrixProjectionImprovement_ALT_distance
#print axioms ThomGame.Analysis.exists_matrixALTSelection_step
#print axioms ThomGame.Analysis.matrixALTSelectionStep_mono
#print axioms ThomGame.Analysis.matrixTraceReal_nonzero_projection_ge_inv
#print axioms ThomGame.Analysis.matrixALTSelectionStep_progress
#print axioms ThomGame.Analysis.exists_matrixALTSelection_terminal_path
#print axioms ThomGame.Analysis.exists_matrixALTSelection_family
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_selection
#check ThomGame.Analysis.matrixALT_lowSpectral_polar_transport
#check ThomGame.Analysis.matrixALTSelectionPotential_increment_ge_source
#check ThomGame.Analysis.exists_matrixALTSelection_family
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_selection

#print axioms ThomGame.Analysis.matrixALTSelection_expansion_of_not_candidate
#print axioms ThomGame.Analysis.matrixALTSelection_terminal_expansion
#print axioms ThomGame.Analysis.matrixALTSelection_minimal_rank_expansion
#print axioms ThomGame.Analysis.rectHSNorm_rectAbs_commutator_sq_le
#print axioms ThomGame.Analysis.matrixIntertwiningEnergy_rectAbs_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_projection_sum_sqrt_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_neg
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_eq_negative_cut
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_sqrt
#print axioms ThomGame.Analysis.exists_matrixClosedLowSpectralCut_energy_le
#print axioms ThomGame.Analysis.exists_matrixClosedLowSpectralCut_sqrt_energy_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_projection_le_trace
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_selected_sum_sqrt_le
#print axioms ThomGame.Analysis.exists_matrixALT_lowCut_energy_le
#print axioms ThomGame.Analysis.exists_matrixALT_terminal_lowCut
#print axioms ThomGame.Analysis.matrixALT_terminal_coverage
#print axioms ThomGame.Analysis.matrixClosedLowSpectralCut_complement_le_square
#print axioms ThomGame.Analysis.matrixTraceReal_lowCut_complement_mul_le
#print axioms ThomGame.Analysis.matrixTraceReal_lowCut_complement_sum_le
#print axioms ThomGame.Analysis.exists_matrixALT_terminal_orthogonalCorrection
#print axioms ThomGame.Analysis.matrixFiniteTrajectory_partialSum
#print axioms ThomGame.Analysis.matrixProjectionImprovement_rank_lt_twice
#print axioms ThomGame.Analysis.exists_matrixALTOrthogonalSelection
#print axioms ThomGame.Analysis.altDecompositionScale_eq
#print axioms ThomGame.Analysis.alt_inverse_eighth_four
#print axioms ThomGame.Analysis.alt_exp_neg_le_inv_sqrt
#print axioms ThomGame.Analysis.alt_nine_exp_neg_le_exp_neg_sqrt
#print axioms ThomGame.Analysis.altDecompositionScale_pos
#print axioms ThomGame.Analysis.altDecompositionScale_small_bounds
#print axioms ThomGame.Analysis.altDecompositionScale_tendsto_zero
#print axioms ThomGame.Analysis.altDecompositionScale_eventually_admissible
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_orthogonalSelection
#check ThomGame.Analysis.matrixALTSelection_terminal_expansion
#check ThomGame.Analysis.exists_matrixALT_terminal_lowCut
#check ThomGame.Analysis.exists_matrixALTOrthogonalSelection
#check ThomGame.Analysis.altDecompositionScale_eventually_admissible
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_orthogonalSelection
#print axioms ThomGame.Analysis.exists_matrixPartition_reducing_unitary
#print axioms ThomGame.Analysis.exists_matrixPartition_reducing_tuple
#print axioms ThomGame.Analysis.half_step_support_error
#print axioms ThomGame.Analysis.matrixHalfProjection_support_bound
#print axioms ThomGame.Analysis.matrixHalfProjection_le_support
#print axioms ThomGame.Analysis.matrixRealSupport_le_projection
#print axioms ThomGame.Analysis.matrixProjection_compression_bounds
#print axioms ThomGame.Analysis.matrixHalfProjection_compression_le
#print axioms ThomGame.Analysis.matrixHalfProjection_compression_rank_le
#print axioms ThomGame.Analysis.matrixHalfProjection_compression_pairing
#print axioms ThomGame.Analysis.matrixHalfProjection_compression_distance_le
#print axioms ThomGame.Analysis.matrixHalfProjection_compression_trace_ge
#print axioms ThomGame.Analysis.rectHSNorm_projection_sum_mul_sq
#print axioms ThomGame.Analysis.rectHSNorm_mul_projection_sum_sq
#print axioms ThomGame.Analysis.rectHSNorm_projection_sum_commutator_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_orthogonal_sum_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_orthogonal_completion_le
#print axioms ThomGame.Analysis.matrixALTSelection_compression_expansion
#print axioms ThomGame.Analysis.MatrixALTOrthogonalSelection.half_rank_lt_selected
#print axioms ThomGame.Analysis.MatrixALTOrthogonalSelection.transported_half_expansion
#print axioms ThomGame.Analysis.MatrixALTOrthogonalSelection.completed_partition_energy
#print axioms ThomGame.Analysis.MatrixALTOrthogonalSelection.exists_reducing_tuple
#print axioms ThomGame.Analysis.rectHSNorm_sub_sq_le
#print axioms ThomGame.Analysis.rectHSNorm_partialIsometry_mul_sq_le
#print axioms ThomGame.Analysis.matrixALT_transport_commutator
#print axioms ThomGame.Analysis.rectHSNorm_ALT_transport_commutator_le
#print axioms ThomGame.Analysis.matrixALTIntertwiningDefect_nonneg
#print axioms ThomGame.Analysis.matrixALTIntertwiningDefect_eq
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_ALT_transport_le
#print axioms ThomGame.Analysis.matrixALTBlockError_nonneg
#print axioms ThomGame.Analysis.MatrixALTOrthogonalSelection.reducing_half_expansion
#print axioms ThomGame.Analysis.rectHSNorm_family_mul_sum_le
#print axioms ThomGame.Analysis.hsNorm_intertwining_family_sum_le
#print axioms ThomGame.Analysis.matrixALTIntertwiningDefect_sum_le
#print axioms ThomGame.Analysis.MatrixALTOrthogonalSelection.block_error_sum_le
#print axioms ThomGame.Analysis.matrixDoubledTuple_perturb_sq_le
#print axioms ThomGame.Analysis.exists_matrixALT_prunedDecomposition
#print axioms ThomGame.Analysis.altBlockErrorBound_tendsto_zero
#print axioms ThomGame.Analysis.altPrunedTraceBound_tendsto_zero
#print axioms ThomGame.Analysis.altPrunedEditBound_tendsto_zero
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_prunedDecomposition
#check ThomGame.Analysis.matrixHalfProjection_compression_distance_le
#check ThomGame.Analysis.MatrixALTOrthogonalSelection.reducing_half_expansion
#check ThomGame.Analysis.exists_matrixALT_prunedDecomposition
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_prunedDecomposition
#print axioms ThomGame.Analysis.matrixRankOneCorner_exists_scalar
#print axioms ThomGame.Analysis.normalizedTrace_projection_ne_zero
#print axioms ThomGame.Analysis.matrixRankOneCorner_eq_trace_scalar
#print axioms ThomGame.Analysis.matrixRankOneCorner_scalar_gap
#print axioms ThomGame.Analysis.matrixBasisProjection_empty
#print axioms ThomGame.Analysis.matrixBasisProjection_singleton_orthogonal
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_eq
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_isStarProjection
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_rank_le
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_rank_eq
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_orthogonal
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_sum
#print axioms ThomGame.Analysis.matrixProjectionRankOnePiece_le
#print axioms ThomGame.Analysis.matrixProjection_sub_identity
#print axioms ThomGame.Analysis.exists_matrixScalarGapPartition_refinement
#print axioms ThomGame.Analysis.exists_matrixScalarGapPartition_identity
#print axioms ThomGame.Analysis.exists_matrixALT_refinement
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_decomposition
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_theorem4_3
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.length_le_of_nonzero
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.exists_nonzero
#print axioms ThomGame.Analysis.hsNorm_tendsto_zero_of_sum_sq
#print axioms ThomGame.Analysis.matrixQuotientMk_tuple_eq_of_sum_sq
#print axioms ThomGame.Analysis.unitarySequenceMk_tuple_eq_of_sum_sq
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_nonzero_representatives
#check ThomGame.Analysis.matrixRankOneCorner_eq_trace_scalar
#check ThomGame.Analysis.exists_matrixALT_refinement
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_theorem4_3
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_nonzero_representatives

#print axioms ThomGame.Analysis.matrixPartitionScalarSum_block_left
#print axioms ThomGame.Analysis.matrixPartitionScalarSum_mul
#print axioms ThomGame.Analysis.matrixPartitionScalarAlgebra_projection_mem
#print axioms ThomGame.Analysis.matrixPartitionScalarSum_mem
#print axioms ThomGame.Analysis.matrixPartitionScalarAlgebra_eq_range
#print axioms ThomGame.Analysis.mem_matrixPartitionScalarAlgebra_iff
#print axioms ThomGame.Analysis.mem_matrixPartitionBlockAlgebra_iff
#print axioms ThomGame.Analysis.matrixPartitionScalarSum_commute
#print axioms ThomGame.Analysis.matrixPartitionScalarAlgebra_commute
#print axioms ThomGame.Analysis.matrixPartitionScalarAlgebra_centralizer
#print axioms ThomGame.Analysis.matrixTraceReal_projection_commutator_cross
#print axioms ThomGame.Analysis.rectHSNorm_projection_commutator_sq
#print axioms ThomGame.Analysis.rectHSNorm_pinching_commutator_sum
#print axioms ThomGame.Analysis.matrixSignSum_unitary
#print axioms ThomGame.Analysis.matrixSignSum_expect_pinching_commutator
#print axioms ThomGame.Analysis.exists_matrixSignSum_pinching_defect_le
#print axioms ThomGame.Analysis.matrixSignSum_sandwich
#print axioms ThomGame.Analysis.matrix_expect_real_smul
#print axioms ThomGame.Analysis.matrixSignSum_expect_sandwich
#print axioms ThomGame.Analysis.matrixBlockPinch_matrixOpNorm_le
#print axioms ThomGame.Analysis.matrixSignSum_mem_scalarAlgebra
#print axioms ThomGame.Analysis.boundedMatrixPinch_apply
#print axioms ThomGame.Analysis.boundedMatrixSign_apply
#print axioms ThomGame.Analysis.boundedMatrixSign_scalar_mem
#print axioms ThomGame.Analysis.boundedMatrixPinch_block_mem
#print axioms ThomGame.Analysis.matrixInternalDiagonal_commute_pinching_tendsto
#print axioms ThomGame.Analysis.matrixInternalBlock_scalar_commute
#print axioms ThomGame.Analysis.matrixInternalDiagonal_centralizer
#print axioms ThomGame.Analysis.cstarMatrix_sum_apply
#print axioms ThomGame.Analysis.matrixUnitaryConjugation_amplification_nonneg
#print axioms ThomGame.Analysis.matrixLazyMarkov_amplification
#print axioms ThomGame.Analysis.matrixLazyMarkov_amplification_nonneg
#print axioms ThomGame.Analysis.matrixLazyMarkovCP_toLinearMap
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_amplification_nonneg
#print axioms ThomGame.Analysis.matrixMarkovPowerCP_toLinearMap
#print axioms ThomGame.Analysis.matrixUnitaryConjugation_bimodule
#print axioms ThomGame.Analysis.matrixUnitary_inv_commute
#print axioms ThomGame.Analysis.matrixLazyMarkov_bimodule
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_bimodule
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_pairing
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.scalar_commute
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.markov_pow_bimodule
#print axioms ThomGame.Analysis.matrixPartitionScalarExpectation_mem
#print axioms ThomGame.Analysis.matrixPartitionScalarExpectation_corner
#print axioms ThomGame.Analysis.matrixPartitionScalarExpectation_block_pairing
#print axioms ThomGame.Analysis.matrixPartitionScalarExpectation_eq_traceProjection
#print axioms ThomGame.Analysis.matrixPartitionScalarExpectation_hsNorm_le
#print axioms ThomGame.Analysis.matrixPartitionScalarExpectation_matrixOpNorm_le
#print axioms ThomGame.Analysis.matrixScalarGapPartition_internal_le_commutant
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_scalar_diagonal
#print axioms ThomGame.Analysis.matrixUnitaryConjugation_sub_le
#print axioms ThomGame.Analysis.hsNorm_finset_sum_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_sub_hsNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_sub_hsNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_sub_mixedNorm_le
#check ThomGame.Analysis.matrixInternalDiagonal_centralizer
#check ThomGame.Analysis.matrixPartitionScalarExpectation_eq_traceProjection
#check ThomGame.Analysis.matrixMarkovPowerCP
#check ThomGame.Analysis.matrixLazyMarkov_pow_sub_mixedNorm_le
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_scalar_diagonal

#print axioms ThomGame.Analysis.positive_operator_restrict_nonneg
#print axioms ThomGame.Analysis.continuousLinearMap_restrict_pow_apply
#print axioms ThomGame.Analysis.positive_operator_norm_le_of_quadratic
#print axioms ThomGame.Analysis.positive_operator_invariant_pow_norm_le
#print axioms ThomGame.Analysis.mem_matrixCornerTraceZeroHilbert
#print axioms ThomGame.Analysis.matrixLazyMarkov_corner_support
#print axioms ThomGame.Analysis.matrixCornerTraceZeroHilbert_invariant
#print axioms ThomGame.Analysis.matrixLazyMarkov_traceZero_corner_pow_le
#print axioms ThomGame.Analysis.matrixCornerCenter_support
#print axioms ThomGame.Analysis.matrixCornerCenter_trace
#print axioms ThomGame.Analysis.matrixTraceProjection_defect_hsNorm_le
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.cornerCenter_hsNorm_le
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_reducing_projection
#print axioms ThomGame.Analysis.matrixLazyMarkov_pow_center
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.corner_markov_pow_scalar_le
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_corner_sum
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.corner_sum_eq
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.corner_center_sum
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.block_scalar_gap
#print axioms ThomGame.Analysis.matrixPartitionScalarAlgebra_le_block
#print axioms ThomGame.Analysis.matrixCoordinateEnergy_tendsto_zero_of_commutant
#print axioms ThomGame.Analysis.matrixScalarGapPartition_block_commutant_mem_diagonal
#print axioms ThomGame.Analysis.matrixScalarGapPartition_internal_block_inf_commutant
#print axioms ThomGame.Analysis.matrixScalarGapPartition_internal_masa
#print axioms ThomGame.Analysis.matrixCornerMarkovError_apply
#print axioms ThomGame.Analysis.matrixScalarCornerError_nonneg
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.corner_markov_error_norm_le
#print axioms ThomGame.Analysis.MatrixScalarGapPartition.scalarCornerError_le
#print axioms ThomGame.Analysis.matrixScalarCornerErrorSequence_nonneg
#print axioms ThomGame.Analysis.matrixScalarCornerErrorSequence_tendsto_zero
#print axioms ThomGame.Analysis.matrixRelativeCommutant_eq_of_tupleClass_eq
#print axioms ThomGame.Analysis.matrixRelativeCommutant_append_self
#print axioms ThomGame.Analysis.matrixScalarGapPartition_internal_maximal
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_masa
#print axioms ThomGame.Analysis.slowDivergingPower_pos
#print axioms ThomGame.Analysis.slowPowerRequirements_eventually
#print axioms ThomGame.Analysis.slowDivergingPower_tendsto
#print axioms ThomGame.Analysis.slowDivergingPower_spec_eventually
#print axioms ThomGame.Analysis.slowDivergingPower_le_eventually
#print axioms ThomGame.Analysis.slowDivergingPower_mul_tendsto_zero
#print axioms ThomGame.Analysis.lazyMarkovWeight_add_self_mul_two
#print axioms ThomGame.Analysis.matrixLazyMarkov_append_self
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_append_self
#print axioms ThomGame.Analysis.matrixMarkovTupleEditBound_nonneg
#print axioms ThomGame.Analysis.matrixMarkovTupleEditBound_tendsto_zero
#print axioms ThomGame.Analysis.matrixMarkovTupleEditBound_tendsto_zero_of_sum_sq
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_sub_mixedNorm_le
#print axioms ThomGame.Analysis.matrixUniformMarkovPower_sub_mixedNorm_tendsto_zero
#print axioms ThomGame.Analysis.exists_matrixALT_corrected_power_expectation
#print axioms ThomGame.Analysis.exists_matrixUltraproduct_ALT_corollary5_1
#print axioms ThomGame.Analysis.UniformMatrixMap.quotientMap_idempotent_iff_defect_tendsto_zero
#print axioms ThomGame.Analysis.UniformMatrixMap.idempotenceDefect_hsNorm_le
#print axioms ThomGame.Analysis.matrixUniformMap_idempotenceDefect_tendsto_zero
#check ThomGame.Analysis.MatrixScalarGapPartition.corner_markov_error_norm_le
#check ThomGame.Analysis.matrixScalarGapPartition_internal_masa
#check ThomGame.Analysis.exists_matrixALT_corrected_power_expectation
#check ThomGame.Analysis.exists_matrixUltraproduct_ALT_corollary5_1
#check ThomGame.Analysis.matrixUniformMap_idempotenceDefect_tendsto_zero

#print axioms ThomGame.Analysis.cstarMatrix_diagonal_nonneg
#print axioms ThomGame.Analysis.cstarMatrix_two_gram_nonneg
#print axioms ThomGame.Analysis.completelyPositiveMap_star
#print axioms ThomGame.Analysis.completelyPositiveMap_schwarz
#print axioms ThomGame.Analysis.completelyPositiveMap_norm_le
#print axioms ThomGame.Analysis.hsNorm_mul_star_eq_star_mul
#print axioms ThomGame.Analysis.matrixUCP_matrixOpNorm_le
#print axioms ThomGame.Analysis.matrixUCP_hsNorm_le
#print axioms ThomGame.Analysis.matrixMapHilbert_apply
#print axioms ThomGame.Analysis.matrixMapHilbert_isSymmetric
#print axioms ThomGame.Analysis.matrixUCP_hilbert_norm_le
#print axioms ThomGame.Analysis.matrixUCP_real_eigenvalue_abs_le_one
#print axioms ThomGame.Analysis.matrixUCP_eigenvector_gram_le
#print axioms ThomGame.Analysis.matrix_positive_corner_moment_bound
#print axioms ThomGame.Analysis.matrixUCP_corner_fourth_moment
#print axioms ThomGame.Analysis.matrix_corner_trace_sq_le
#print axioms ThomGame.Analysis.matrixUCP_left_corner_fourth_moment
#print axioms ThomGame.Analysis.matrixUCP_rectangular_moment_bounds
#print axioms ThomGame.Analysis.matrixProjection_trace_min_max_ratio
#print axioms ThomGame.Analysis.matrixUCP_rectangular_ALT_5_4
#print axioms ThomGame.Analysis.mem_matrixRectangleHilbert
#print axioms ThomGame.Analysis.matrixBimodule_rectangle_invariant
#print axioms ThomGame.Analysis.matrixRectangleHilbert_invariant
#print axioms ThomGame.Analysis.matrixRectangleHilbertMap_isSymmetric
#print axioms ThomGame.Analysis.exists_matrixRectangle_orthonormal_eigenbasis
#print axioms ThomGame.Analysis.exists_matrixRectangle_rescaled_eigenvector
#print axioms ThomGame.Analysis.matrixCornerMapError_apply
#print axioms ThomGame.Analysis.matrixCornerMapError_markov
#print axioms ThomGame.Analysis.matrixScalarMixingError_nonneg
#print axioms ThomGame.Analysis.matrixCornerMapError_norm_le
#print axioms ThomGame.Analysis.matrixScalarMixingError_hsNorm_le
#print axioms ThomGame.Analysis.matrixScalarMixingError_le
#print axioms ThomGame.Analysis.matrixScalarMixingError_markov
#print axioms ThomGame.Analysis.exists_matrixScalarBimodule_rectangular_eigenbasis
#print axioms ThomGame.Analysis.exists_matrixUCP_rectangular_ALT_5_4

#print axioms ThomGame.Analysis.realRightNormFactor_mem_Icc
#print axioms ThomGame.Analysis.realRightNormFactor_tail_fourth
#print axioms ThomGame.Analysis.matrixRightNormClamp_tail_gram
#print axioms ThomGame.Analysis.matrixRightNormClamp_tail_fourth
#print axioms ThomGame.Analysis.matrixRightNormClamp_rectangle
#print axioms ThomGame.Analysis.matrixALTTruncation_cutoff
#print axioms ThomGame.Analysis.matrixALTTruncation_tail
#print axioms ThomGame.Analysis.matrixALTTruncation_pairing
#print axioms ThomGame.Analysis.matrixALTTruncationContraction_norm
#print axioms ThomGame.Analysis.matrixALTTruncationContraction_rectangle
#print axioms ThomGame.Analysis.matrix_eigenvector_defect_pairing
#print axioms ThomGame.Analysis.matrix_eigenvector_defect_sq
#print axioms ThomGame.Analysis.matrixALTTruncationContraction_pairing
#print axioms ThomGame.Analysis.matrixALTTruncationContraction_defect
#print axioms ThomGame.Analysis.alt_bad_eigenvalue_gap
#print axioms ThomGame.Analysis.alt_bad_eigenvalue_polynomial
#print axioms ThomGame.Analysis.matrixALT_bad_eigenvalue_defect
#print axioms ThomGame.Analysis.exists_matrixALT_bad_rectangle_contraction
#print axioms ThomGame.Analysis.matrixScalarCorner_eigenvalue_dichotomy
#print axioms ThomGame.Analysis.matrixScalarMixingError_diagonal_eigenvalue
#print axioms ThomGame.Analysis.matrixALT_no_bad_diagonal
#print axioms ThomGame.Analysis.matrixUCP_rectangular_eigenvector_star
#print axioms ThomGame.Analysis.mem_finitePairEndpoints
#print axioms ThomGame.Analysis.mem_finiteMatchingVertices
#print axioms ThomGame.Analysis.exists_finitePairMatching_cover
#print axioms ThomGame.Analysis.finitePairMatching_endpoint_weight
#print axioms ThomGame.Analysis.finitePairMatching_fst_injective
#print axioms ThomGame.Analysis.finitePairMatching_snd_injective
#print axioms ThomGame.Analysis.matrixContraction_gram_le_support
#print axioms ThomGame.Analysis.matrixOrthogonalRectangles_sum_contraction
#print axioms ThomGame.Analysis.matrixOrthogonalRectangles_sum_hsNorm_sq
#print axioms ThomGame.Analysis.matrixOrthogonalRectangles_defect_sum
#print axioms ThomGame.Analysis.matrixOrthogonalRectangles_defect_sum_le
#print axioms ThomGame.Analysis.matrixALTBadPair_irrefl
#print axioms ThomGame.Analysis.matrixALT_matching_endpoint_trace
#print axioms ThomGame.Analysis.exists_matrixALT_retained_eigenvalue_bands
#print axioms ThomGame.Analysis.altReconstructionThreshold_pos
#print axioms ThomGame.Analysis.altReconstructionThreshold_fourth
#print axioms ThomGame.Analysis.altReconstructionThreshold_bounds
#print axioms ThomGame.Analysis.altReconstructionThreshold_tendsto
#print axioms ThomGame.Analysis.altReconstructionThreshold_eventually_small
#print axioms ThomGame.Analysis.alt_reconstruction_removal_cost
#print axioms ThomGame.Analysis.matrixRetainedBlockProjection_isStarProjection
#print axioms ThomGame.Analysis.matrixRetainedBlockProjection_trace
#print axioms ThomGame.Analysis.matrixRetainedBlockProjection_sum
#print axioms ThomGame.Analysis.matrixRetainedBlockProjection_mul_block
#print axioms ThomGame.Analysis.exists_matrixALT_retained_projection
#print axioms ThomGame.Analysis.matrixRectangleHilbertMap_spectrum_bands
#print axioms ThomGame.Analysis.matrixScalarBimoduleRectangleMap_spectrum_bands
#print axioms ThomGame.Analysis.exists_matrixALT_spectral_pruning

#print axioms ThomGame.Analysis.exists_matrixProjection_intermediate_rank
#print axioms ThomGame.Analysis.matrixProjection_eq_of_le_rank_eq
#print axioms ThomGame.Analysis.exists_matrixPolar_min_rank_completion
#print axioms ThomGame.Analysis.matrix_positive_fourth_moment_order
#print axioms ThomGame.Analysis.matrixRectAbs_fourth_trace
#print axioms ThomGame.Analysis.matrixPolarCompletion_fourth_distance
#print axioms ThomGame.Analysis.alt_high_eigenvalue_gap
#print axioms ThomGame.Analysis.matrixPolarCompletion_high_distance
#print axioms ThomGame.Analysis.matrixUCP_near_eigenvector_fixed_error
#print axioms ThomGame.Analysis.exists_matrixUCP_high_polar_completion
#print axioms ThomGame.Analysis.matrixChoi_input_nonneg
#print axioms ThomGame.Analysis.exists_matrix_kraus
#print axioms ThomGame.Analysis.matrixChannelEnergy_kraus
#print axioms ThomGame.Analysis.matrixKrausDifferential_norm_sq
#print axioms ThomGame.Analysis.matrixUCP_energy_nonneg
#print axioms ThomGame.Analysis.matrixUCP_fixed_error_sq_le_energy
#print axioms ThomGame.Analysis.matrixChannelEnergy_star
#print axioms ThomGame.Analysis.matrixKrausDifferential_norm_eq
#print axioms ThomGame.Analysis.matrixUCP_energy_sqrt_add_le
#print axioms ThomGame.Analysis.matrixUCP_energy_sqrt_smul
#print axioms ThomGame.Analysis.matrixUCP_energySeminorm_apply
#print axioms ThomGame.Analysis.matrixUCP_energy_le_two_norm_sq
#print axioms ThomGame.Analysis.matrixUCP_energy_sqrt_le
#print axioms ThomGame.Analysis.matrixKrausDifferential_mul_le
#print axioms ThomGame.Analysis.matrixUCP_energy_sqrt_mul_le
#print axioms ThomGame.Analysis.matrixUCP_fixed_error_le_sqrt_energy
#print axioms ThomGame.Analysis.matrixUCP_product_fixed_error
#print axioms ThomGame.Analysis.matrixChannelEnergy_real_eigenvector
#print axioms ThomGame.Analysis.matrixUCP_energy_perturbation
#print axioms ThomGame.Analysis.matrixUCP_high_polar_energy
#print axioms ThomGame.Analysis.hsNorm_sub_sq

#print axioms ThomGame.Analysis.matrixProjection_overlap_trace
#print axioms ThomGame.Analysis.hsNorm_star_mul_sq_trace
#print axioms ThomGame.Analysis.matrixPartialIsometries_overlap_mass
#print axioms ThomGame.Analysis.norm_normalizedTrace_pairing_le
#print axioms ThomGame.Analysis.matrixOrthogonal_perturbed_pairing
#print axioms ThomGame.Analysis.matrixOrthogonal_close_pairing_sq
#print axioms ThomGame.Analysis.matrixProjection_trace_re_pos
#print axioms ThomGame.Analysis.matrixCorner_scalar_norm_sq
#print axioms ThomGame.Analysis.hsNorm_add_sq_le_two
#print axioms ThomGame.Analysis.matrixCorner_mass_le_scalar_error
#print axioms ThomGame.Analysis.matrixUCP_product_fixed_error_sq
#print axioms ThomGame.Analysis.matrixHighPolar_product_scalar_error
#print axioms ThomGame.Analysis.matrixHighPolar_orthogonality_obstruction
#print axioms ThomGame.Analysis.exists_matrixHS_positive_rescaling
#print axioms ThomGame.Analysis.normalizedTrace_pairing_smul
#print axioms ThomGame.Analysis.matrixUCP_no_orthogonal_normalized_high_rectangle
#print axioms ThomGame.Analysis.matrixUCP_no_orthogonal_high_rectangle
#print axioms ThomGame.Analysis.matrixUCP_high_rectangle_unique
#print axioms ThomGame.Analysis.orthonormal_operator_norm_le
#print axioms ThomGame.Analysis.symmetric_eigenbasis_norm_le
#print axioms ThomGame.Analysis.symmetric_eigenbasis_sub_lineProjection_norm_le
#print axioms ThomGame.Analysis.normalized_vectors_distance_le
#print axioms ThomGame.Analysis.unit_lineProjection_distance_le
#print axioms ThomGame.Analysis.lineProjection_distance_le
#print axioms ThomGame.Analysis.lineProjection_distance_sq
#print axioms ThomGame.Analysis.exists_matrixUCP_rectangle_spectral_bounds
#print axioms ThomGame.Analysis.matrixRectangleVector_ne_zero
#print axioms ThomGame.Analysis.matrixRectangleVector_norm
#print axioms ThomGame.Analysis.matrixRectangleLineProjection_distance_sq
#print axioms ThomGame.Analysis.matrixUCP_high_rectangle_projection_bound
#print axioms ThomGame.Analysis.exists_matrixUCP_high_polar_approximation
#print axioms ThomGame.Analysis.matrixUCP_no_high_rectangle_norm_le
#print axioms ThomGame.Analysis.exists_matrixUCP_high_rectangle_approximation

#print axioms ThomGame.Analysis.highRelation_triple_overlap
#print axioms ThomGame.Analysis.highRelation_low_product_impossible
#print axioms ThomGame.Analysis.matrixRectangleHilbertMap_bound
#print axioms ThomGame.Analysis.matrixRectangle_fixed_error_lower
#print axioms ThomGame.Analysis.matrixUCP_high_rectangle_trans
#print axioms ThomGame.Analysis.matrixRectangleHasHighEigenvalue_refl
#print axioms ThomGame.Analysis.matrixUCP_high_rectangle_symm
#print axioms ThomGame.Analysis.matrixBimodule_fixes_projection
#print axioms ThomGame.Analysis.matrixUCP_high_rectangle_equivalence
#print axioms ThomGame.Analysis.matrixUCP_retained_high_equivalence
#print axioms ThomGame.Analysis.exists_finite_class_minimum
#print axioms ThomGame.Analysis.exists_matrixALT_retained_equivalence
#print axioms ThomGame.Analysis.exists_matrixUCP_high_smaller_isometry
#print axioms ThomGame.Analysis.exists_matrixALT_class_isometries
#print axioms ThomGame.Analysis.matrixSupported_pairing_zero
#print axioms ThomGame.Analysis.matrixIsometryUnit_star
#print axioms ThomGame.Analysis.matrixIsometryUnit_support
#print axioms ThomGame.Analysis.matrixIsometryUnit_mul
#print axioms ThomGame.Analysis.matrixIsometryUnit_zero_of_initial_orthogonal
#print axioms ThomGame.Analysis.matrixIsometryUnit_mass
#print axioms ThomGame.Analysis.matrixIsometryUnit_nonzero
#print axioms ThomGame.Analysis.matrixIsometryUnit_fixed_error
#print axioms ThomGame.Analysis.exists_matrixALT_class_matrix_units
#print axioms ThomGame.Analysis.matrixSubprojection_sum_trace_loss
#print axioms ThomGame.Analysis.exists_matrixALT_pruned_matrix_units

#print axioms ThomGame.Analysis.lineProjection_distance_le_residual
#print axioms ThomGame.Analysis.operator_lineProjection_of_fixed_error
#print axioms ThomGame.Analysis.matrixRectangle_lineProjection_of_fixed_error
#print axioms ThomGame.Analysis.matrixUCP_high_unit_projection_bound
#print axioms ThomGame.Analysis.matrixUnitSpan_unit_mem
#print axioms ThomGame.Analysis.matrixUnitSpan_mul
#print axioms ThomGame.Analysis.matrixUnitSpan_star
#print axioms ThomGame.Analysis.mem_matrixUnitSpanAlgebra_iff
#print axioms ThomGame.Analysis.matrixUnitSpan_diagonal_sum_mem
#print axioms ThomGame.Analysis.matrixUnitSpan_diagonal_identity
#print axioms ThomGame.Analysis.matrixUnitSpan_diagonal_projection
#print axioms ThomGame.Analysis.matrixComplementaryCorners_mul_zero
#print axioms ThomGame.Analysis.matrixCornerCompletion_one_mem
#print axioms ThomGame.Analysis.mem_matrixCornerCompletionAlgebra_iff
#print axioms ThomGame.Analysis.matrixCornerCompletionAlgebra_mem_of_commute
#print axioms ThomGame.Analysis.mem_matrixUnitCompletionAlgebra_iff
#print axioms ThomGame.Analysis.matrixUnitCompletionAlgebra_unit_mem
#print axioms ThomGame.Analysis.matrixUnitCompletionAlgebra_complement_mem
#print axioms ThomGame.Analysis.matrixRectangleLineProjection_eq_zero
#print axioms ThomGame.Analysis.matrixUCP_unit_or_zero_projection_bound
#print axioms ThomGame.Analysis.exists_matrixALT_coordinate_algebra
#print axioms ThomGame.Analysis.matrixUnitCompletionAlgebra_original_projection_mem
#print axioms ThomGame.Analysis.matrixPartitionScalarAlgebra_le_unitCompletion
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_embedding
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_mem
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_eq_self
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_orthogonal
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_unique
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_hsNorm_le
#print axioms ThomGame.Analysis.matrixRectangle_pairing_compress_left
#print axioms ThomGame.Analysis.matrixRectangle_pairing_compress_right
#print axioms ThomGame.Analysis.matrixCornerCompletion_expectation
#print axioms ThomGame.Analysis.matrixUnitCompletionAlgebra_expectation

#print axioms ThomGame.Analysis.matrixUnitSpan_compression_mem_line
#print axioms ThomGame.Analysis.matrixUnitSpan_rectangle_eq_line
#print axioms ThomGame.Analysis.matrixSubmoduleTraceHilbert_singleton
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_singleton
#print axioms ThomGame.Analysis.matrixRectangleLineProjection_apply_matrix
#print axioms ThomGame.Analysis.matrixUnitSpan_projection_rectangle
#print axioms ThomGame.Analysis.matrixUnitSpan_projection_invariant
#print axioms ThomGame.Analysis.matrixRectangle_line_error_bound
#print axioms ThomGame.Analysis.matrixUnitSpan_rectangle_error_bound
#print axioms ThomGame.Analysis.matrixOrthogonalRectangles_sum_hsNorm_sq_right
#print axioms ThomGame.Analysis.matrixRectangles_sum_hsNorm_sq
#print axioms ThomGame.Analysis.matrixRectangles_sum_compression
#print axioms ThomGame.Analysis.matrixRectangles_map_sum_bound
#print axioms ThomGame.Analysis.matrixRectangles_map_corner_bound
#print axioms ThomGame.Analysis.matrixUnitSpan_corner_error_bound
#print axioms ThomGame.Analysis.matrixSubmoduleTraceProjection_compression
#print axioms ThomGame.Analysis.matrixUnitSpan_le_rectangle_sum
#print axioms ThomGame.Analysis.matrixUnitSpan_projection_compression
#print axioms ThomGame.Analysis.hsNorm_add_sq_of_gram_zero
#print axioms ThomGame.Analysis.matrixProjection_compression_hsNorm_le
#print axioms ThomGame.Analysis.matrixProjection_compression_trace_bound
#print axioms ThomGame.Analysis.matrixProjection_compression_loss_sq
#print axioms ThomGame.Analysis.matrixProjection_compression_loss
#print axioms ThomGame.Analysis.matrixUnitSpan_completed_expectation_bound
#print axioms ThomGame.Analysis.matrixALT_trace_loss_error_bound
#print axioms ThomGame.Analysis.exists_matrixALT_approximating_algebra
#print axioms ThomGame.Analysis.exists_matrixALT_expectation_approximation
#print axioms ThomGame.Analysis.matrixMixedNorm_approximation_induces_expectation
#print axioms ThomGame.Analysis.exists_matrixALT_internal_relative_commutant
#print axioms ThomGame.Analysis.exists_matrixALT_internal_range

#print axioms ThomGame.Analysis.exists_fixed_mem_closedConvexHull
#print axioms ThomGame.Analysis.exists_fixed_near_of_invariant_set
#print axioms ThomGame.Analysis.mem_starSubalgebraCenter_iff
#print axioms ThomGame.Analysis.starSubalgebraCenter_le
#print axioms ThomGame.Analysis.matrixSubalgebraUnitary_val
#print axioms ThomGame.Analysis.matrixSubalgebraUnitary_one
#print axioms ThomGame.Analysis.matrixSubalgebraUnitary_mul
#print axioms ThomGame.Analysis.matrixSubalgebra_commute_of_unitaries
#print axioms ThomGame.Analysis.matrixSubalgebraCenter_mem_of_unitaries
#print axioms ThomGame.Analysis.exists_matrixCentral_near_of_commutator_bound
#print axioms ThomGame.Analysis.matrixTraceProjection_bestApproximation
#print axioms ThomGame.Analysis.matrixCenterProjection_error_le
#print axioms ThomGame.Analysis.exists_matrixUnitary_detecting_center_distance
#print axioms ThomGame.Analysis.matrixInternal_center_distance_tendsto
#print axioms ThomGame.Analysis.matrixInternalCenters_commute
#print axioms ThomGame.Analysis.matrixInternalQuotient_center
#print axioms ThomGame.Analysis.exists_matrixALT_theorem5_2
#print axioms ThomGame.Analysis.exists_matrixALT_internal_relative_commutant_and_center

#print axioms ThomGame.Analysis.sqrt_sub_one_abs_le
#print axioms ThomGame.Analysis.matrixRectAbs_sub_one_le_gram
#print axioms ThomGame.Analysis.exists_matrixUnitary_close_of_gram
#print axioms ThomGame.Analysis.exists_unitarySequence_close_of_gram
#print axioms ThomGame.Analysis.exists_matrixQuotient_unitary_lift
#print axioms ThomGame.Analysis.unitarySequenceToAlgebra_surjective
#print axioms ThomGame.Analysis.unitaryQuotientEmbedding_surjective
#print axioms ThomGame.Analysis.unitaryQuotientEquiv_apply
#print axioms ThomGame.Analysis.unitaryQuotientEquiv_mk
#print axioms ThomGame.Analysis.matrixFiniteUnitaryHom_surjective
#print axioms ThomGame.Analysis.matrixFiniteUnitaryEquiv_apply
#print axioms ThomGame.Analysis.unitaryQuotientFiniteEmbedding_surjective
#print axioms ThomGame.Analysis.unitaryQuotientFiniteEquiv_apply
#print axioms ThomGame.Analysis.unitaryQuotientFiniteEquiv_mk
#print axioms ThomGame.Analysis.unitaryQuotientFiniteEquiv_trace
#print axioms ThomGame.Analysis.approximatelyTrivial_matrixQuotient_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_iff_matrixQuotient_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_finiteAlgebra_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_iff_finiteAlgebra_killed
#print axioms ThomGame.Analysis.approximatelyTrivial_iff_finiteAlgebra_hyperfilter_killed

#print axioms ThomGame.Analysis.mem_matrixSubalgebraCommutant_iff
#print axioms ThomGame.Analysis.exists_matrixCommutant_near_of_commutator_bound
#print axioms ThomGame.Analysis.matrixCommutantProjection_error_le
#print axioms ThomGame.Analysis.exists_matrixUnitary_detecting_commutant_distance
#print axioms ThomGame.Analysis.mem_matrixInternalCommutant_iff
#print axioms ThomGame.Analysis.matrixInternal_commutant_distance_tendsto
#print axioms ThomGame.Analysis.matrixInternalCommutants_commute
#print axioms ThomGame.Analysis.matrixInternalQuotient_commutant
#print axioms ThomGame.Analysis.matrixFiniteEmbedding_mem_internalCommutant_iff
#print axioms ThomGame.Analysis.matrixInternalFiniteAlgebra_commutant
#print axioms ThomGame.Analysis.matrixInternalFiniteAlgebra_center
#print axioms ThomGame.Analysis.exists_matrixALT_finite_internal_relative_commutant_and_center

#print axioms ThomGame.Analysis.matrixRectAbs_mem_subalgebra
#print axioms ThomGame.Analysis.matrixRectPolar_mem_subalgebra
#print axioms ThomGame.Analysis.matrixRectPolar_mem_unitary_of_isUnit
#print axioms ThomGame.Analysis.exists_matrixSubalgebraUnitary_close_of_isUnit
#print axioms ThomGame.Analysis.matrixSubalgebra_mem_closure_isUnit
#print axioms ThomGame.Analysis.exists_matrixSubalgebra_invertible_near
#print axioms ThomGame.Analysis.matrixSubalgebra_unitaries_isCompact
#print axioms ThomGame.Analysis.exists_matrixSubalgebraUnitary_close_of_gram
#print axioms ThomGame.Analysis.exists_internalUnitarySequence_close_of_gram
#print axioms ThomGame.Analysis.exists_matrixInternal_unitary_lift
#print axioms ThomGame.Analysis.exists_matrixInternalCommutant_unitary_lift
#print axioms ThomGame.Analysis.exists_matrixFiniteInternal_unitary_lift
#print axioms ThomGame.Analysis.exists_matrixFiniteInternalCommutant_unitary_lift
#print axioms ThomGame.Analysis.matrixNearInclusionError_nonneg
#print axioms ThomGame.Analysis.matrixNearInclusionError_mem_bound
#print axioms ThomGame.Analysis.exists_matrixNearInclusion_maximizer
#print axioms ThomGame.Analysis.matrixNearInclusion_iff_error_le
#print axioms ThomGame.Analysis.matrixInternal_le_iff_nearInclusionError_tendsto
#print axioms ThomGame.Analysis.exists_matrixNearInclusion_errors_of_internal_le
#print axioms ThomGame.Analysis.matrixInternal_le_of_nearInclusion_errors
#print axioms ThomGame.Analysis.matrixInternalFiniteAlgebra_le_iff
#print axioms ThomGame.Analysis.matrixInternalFinite_le_iff_nearInclusionError_tendsto
#print axioms ThomGame.Analysis.exists_matrixNearInclusion_errors_of_finiteInternal_le
#print axioms ThomGame.Analysis.matrixBlockFlatten_apply
#print axioms ThomGame.Analysis.matrixBlockFlatten_trace
#print axioms ThomGame.Analysis.matrixBlockFlatten_normalizedTrace
#print axioms ThomGame.Analysis.mem_matrixBlockSubalgebra
#print axioms ThomGame.Analysis.matrixBlockFlatten_mem_amplified
#print axioms ThomGame.Analysis.matrixTraceProjection_amplified
#print axioms ThomGame.Analysis.matrixTraceProjection_amplification_nonneg
#print axioms ThomGame.Analysis.matrixConditionalExpectationCP_apply
#print axioms ThomGame.Analysis.exists_matrixTraceProjection_kraus
#print axioms ThomGame.Analysis.matrixDiagonalRepresentation_apply
#print axioms ThomGame.Analysis.matrixDiagonalRepresentation_mul_column
#print axioms ThomGame.Analysis.matrixKrausColumn_inner
#print axioms ThomGame.Analysis.matrixKrausColumn_compression
#print axioms ThomGame.Analysis.exists_matrixStinespring
#print axioms ThomGame.Analysis.matrixStinespring_defect_gram
#print axioms ThomGame.Analysis.matrixStinespring_intertwines_of_gram
#print axioms ThomGame.Analysis.matrixStinespring_expectation_intertwines
#print axioms ThomGame.Analysis.matrixStinespring_expectation_defect_sq
#print axioms ThomGame.Analysis.matrixStinespring_expectation_nearInclusion_bound
#print axioms ThomGame.Analysis.exists_matrixSubalgebra_choi_factor
#print axioms ThomGame.Analysis.matrixChoiRightRepresentation_apply
#print axioms ThomGame.Analysis.matrixChoi_representations_commute
#print axioms ThomGame.Analysis.matrixChoiRightRepresentation_intertwines
#print axioms ThomGame.Analysis.matrixStinespring_range_projection
#print axioms ThomGame.Analysis.matrixStinespring_range_commutes
#print axioms ThomGame.Analysis.matrixStinespring_range_trace
#print axioms ThomGame.Analysis.exists_matrixRelativeStinespring
#print axioms ThomGame.Analysis.exists_matrixNearInclusion_relativeDilation
#print axioms ThomGame.Analysis.matrixKraus_of_choi_factor
#print axioms ThomGame.Analysis.matrixSubalgebraConjugation_fixes_commutant
#print axioms ThomGame.Analysis.matrixCommutantProjection_conjugation
#print axioms ThomGame.Analysis.matrixCommutantProjection_mem_closedConvexHull
#print axioms ThomGame.Analysis.matrixCommutantProjection_linear_lower_bound
#print axioms ThomGame.Analysis.matrixTraceReal_eq_of_normalizedTrace_eq
#print axioms ThomGame.Analysis.matrixTraceProjection_traceReal
#print axioms ThomGame.Analysis.matrixTraceProjection_traceReal_pairing
#print axioms ThomGame.Analysis.matrixTraceProjection_projection_bounds
#print axioms ThomGame.Analysis.matrixTraceProjection_traceReal_square
#print axioms ThomGame.Analysis.matrixTraceProjection_projection_variance
#print axioms ThomGame.Analysis.matrixTraceProjection_preserves_commutation
#print axioms ThomGame.Analysis.matrixHalfProjection_expectation_mem
#print axioms ThomGame.Analysis.matrixHalfProjection_expectation_distance_le
#print axioms ThomGame.Analysis.matrixHalfProjection_expectation_trace_error_le
#print axioms ThomGame.Analysis.matrixCommutantProjection_variance_le
#print axioms ThomGame.Analysis.exists_matrixCommutant_roundedProjection
#print axioms ThomGame.Analysis.exists_matrixImage_unitary_preimage
#print axioms ThomGame.Analysis.matrixStinespring_range_overlap
#print axioms ThomGame.Analysis.matrixTraceProjection_unitary_pythagoras
#print axioms ThomGame.Analysis.matrixStinespring_nearInclusion_orbit_overlap
#print axioms ThomGame.Analysis.exists_matrixStinespring_averaged_cut
#print axioms ThomGame.Analysis.matrixReindex_mul
#print axioms ThomGame.Analysis.matrixDiagonalRepresentation_injective
#print axioms ThomGame.Analysis.exists_matrixRelativeStinespring_fin
#print axioms ThomGame.Analysis.matrixIsometry_cut_loss_le_distance
#print axioms ThomGame.Analysis.exists_matrixThomSpectralData
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cut_rank_pos
#print axioms ThomGame.Analysis.MatrixThomSpectralData.dimension_error_absolute
#print axioms ThomGame.Analysis.matrixRectPolar_exact_intertwining
#print axioms ThomGame.Analysis.matrixRectPolar_gram_le_initial
#print axioms ThomGame.Analysis.matrixCutIsometry_polar_support
#print axioms ThomGame.Analysis.matrixCutIsometry_gram_loss
#print axioms ThomGame.Analysis.matrixCutIsometry_polar_distance_le
#print axioms ThomGame.Analysis.matrixCutIsometry_polar_rank_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.polar_correction
#print axioms ThomGame.Analysis.matrixRectangular_intertwining_perturbation
#print axioms ThomGame.Analysis.MatrixThomSpectralData.polar_intertwining_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.polar_rank_lower
#print axioms ThomGame.Analysis.matrixProjectionFinFrame_initial
#print axioms ThomGame.Analysis.matrixProjectionFinFrame_final
#print axioms ThomGame.Analysis.matrixFrame_reducing_intertwines
#print axioms ThomGame.Analysis.matrixFrame_reducing_adjoint_intertwines
#print axioms ThomGame.Analysis.matrixFrame_reducing_mul
#print axioms ThomGame.Analysis.matrixReducingRepresentation_apply
#print axioms ThomGame.Analysis.matrixFrame_compressions_commute
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutFrame_initial
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutFrame_final
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutSourceRepresentation_apply
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutCommutantRepresentation_apply
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutSourceRepresentation_intertwines
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutCommutantRepresentation_intertwines
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutRepresentations_commute
#print axioms ThomGame.Analysis.MatrixThomSpectralData.correctedSourceAlgebra_le_target
#print axioms ThomGame.Analysis.matrixFrame_supported_lift
#print axioms ThomGame.Analysis.matrixFrame_supported_gram
#print axioms ThomGame.Analysis.matrixFrame_supported_rank
#print axioms ThomGame.Analysis.matrixFrame_supported_hsNorm
#print axioms ThomGame.Analysis.matrixFrame_supported_partialIsometry
#print axioms ThomGame.Analysis.matrixFrame_supported_intertwining_lift
#print axioms ThomGame.Analysis.matrixFrame_supported_intertwining_norm
#print axioms ThomGame.Analysis.matrixFrame_supported_exact_intertwining
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_lift
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_gram
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_partialIsometry
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_rank
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_rank_lower
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_distance
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_common_intertwines
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_commutant_intertwines
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_intertwining_error
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_intertwining_bound
#print axioms ThomGame.Analysis.matrixStarIntertwining_support_commutation
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_commutant_supports
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_final_mem_target
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_common_supports
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_initial_complement_rank
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_final_complement_rank
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_complement_trace_bounds
#print axioms ThomGame.Analysis.exists_matrixThomCompressedCorrection
#print axioms ThomGame.Analysis.matrixThom_cut_dimension_ratio_tendsto
#print axioms ThomGame.Analysis.matrixThom_cut_complement_traces_tendsto
#print axioms ThomGame.Analysis.matrixThom_cut_intertwining_tendsto
#print axioms ThomGame.Analysis.rectangular_normalized_trace_gram
#print axioms ThomGame.Analysis.finiteRectMatrixHilbert_inner
#print axioms ThomGame.Analysis.finiteRectMatrixHilbert_norm
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_apply
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_one
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_mul
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_hsNorm
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_defect_norm
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_displacement_le
#print axioms ThomGame.Analysis.matrixRectangular_intertwines_of_unitaries
#print axioms ThomGame.Analysis.exists_matrixRectangular_average
#print axioms ThomGame.Analysis.matrixIsometry_rank_defect_le_distance
#print axioms ThomGame.Analysis.matrixIsometry_rank_lower_of_distance
#print axioms ThomGame.Analysis.matrix_closedConvexHull_preserves_range
#print axioms ThomGame.Analysis.matrixRectangularUnitaryAction_preserves_range
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cut_isometry_distance
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cut_unitary_orbit_distance
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exists_exact_intertwiner_in_dilation
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exists_exact_intertwiner
#print axioms ThomGame.Analysis.matrixRepresentationIntertwiner_polar
#print axioms ThomGame.Analysis.matrixRepresentationIntertwiner_gram_commutants
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactIntertwiner_spec
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactPolarIntertwiner_intertwines
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactPolarIntertwiner_supports
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactPolarIntertwiner_rank_lower
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactPolarIntertwiner_complement_ranks
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactPolarIntertwiner_complement_traces
#print axioms ThomGame.Analysis.MatrixThomSpectralData.exactIntertwiner_rank_ratio_bound
#print axioms ThomGame.Analysis.matrixThom_exact_intertwiner_distance_tendsto
#print axioms ThomGame.Analysis.matrixThom_exact_intertwiner_rank_ratio_tendsto
#print axioms ThomGame.Analysis.matrixThom_exact_intertwiner_complement_traces_tendsto
#print axioms ThomGame.Analysis.matrixKraus_fixed_iff_commute
#print axioms ThomGame.Analysis.exists_matrixTraceProjection_commutant_kraus
#print axioms ThomGame.Analysis.matrixSubalgebra_mem_of_bicommutant
#print axioms ThomGame.Analysis.matrixSubalgebra_le_bicommutant
#print axioms ThomGame.Analysis.matrixSubalgebra_bicommutant_eq
#print axioms ThomGame.Analysis.mem_matrixSubalgebraCorner
#print axioms ThomGame.Analysis.matrixSubalgebraCorner_compression_mem
#print axioms ThomGame.Analysis.matrixSubalgebraCorner_compression_eq
#print axioms ThomGame.Analysis.matrixSubalgebraCorner_eq_compressions
#print axioms ThomGame.Analysis.matrixRepresentationIntertwiner_adjoint
#print axioms ThomGame.Analysis.matrixCommutantIntertwiner_initial_mem
#print axioms ThomGame.Analysis.matrixCommutantIntertwiner_final_mem
#print axioms ThomGame.Analysis.matrixCommutantIntertwiner_push_mem
#print axioms ThomGame.Analysis.matrixCommutantIntertwiner_pull_mem
#print axioms ThomGame.Analysis.matrixPartialIsometry_sandwich_support
#print axioms ThomGame.Analysis.matrixSandwich_inverse_of_support
#print axioms ThomGame.Analysis.matrixSandwich_mul_of_support
#print axioms ThomGame.Analysis.matrixSandwich_star
#print axioms ThomGame.Analysis.matrixCommutantIntertwiner_push_corner
#print axioms ThomGame.Analysis.matrixCommutantIntertwiner_pull_corner
#print axioms ThomGame.Analysis.matrixCommutantCornerEquiv_apply
#print axioms ThomGame.Analysis.matrixCommutantCornerEquiv_image
#print axioms ThomGame.Analysis.matrixRectPartialIsometry_norm_le_one
#print axioms ThomGame.Analysis.matrixPartialIsometry_sandwich_norm_le
#print axioms ThomGame.Analysis.matrixPartialIsometry_sandwich_norm_eq
#print axioms ThomGame.Analysis.matrixSandwich_trace_of_support
#print axioms ThomGame.Analysis.matrixSandwich_hsNorm_of_support
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_initial_mem
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_cornerEquiv_apply
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_corner_image
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_compressed_algebras
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_corner_norm
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_corner_trace
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_corner_hsNorm
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_corner_unitBall_image
#print axioms ThomGame.Analysis.rectHSNorm_projection_sq
#print axioms ThomGame.Analysis.rectHSNorm_projection_compression_le
#print axioms ThomGame.Analysis.rectHSNorm_projection_compression_loss_sq
#print axioms ThomGame.Analysis.rectHSNorm_projection_compression_loss
#print axioms ThomGame.Analysis.matrixProjection_compression_opNorm_le
#print axioms ThomGame.Analysis.matrixSubalgebraCorner_unitBall_compression_image
#print axioms ThomGame.Analysis.matrixSubalgebraCorner_unitBall_approximation
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_source_compression_loss_sq
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_target_compression_loss_sq
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_source_compression_loss
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_target_compression_loss
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_push_contraction
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_pull_contraction
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_source_roundtrip_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.cutPolar_target_roundtrip_bound
#print axioms ThomGame.Analysis.matrixThom_source_compression_tendsto
#print axioms ThomGame.Analysis.matrixThom_target_compression_tendsto
#print axioms ThomGame.Analysis.matrixThom_source_roundtrip_tendsto
#print axioms ThomGame.Analysis.matrixThom_target_roundtrip_tendsto
#print axioms ThomGame.Analysis.matrixProjectionFinFrame_left_support
#print axioms ThomGame.Analysis.matrixProjectionFinFrame_mul_zero
#print axioms ThomGame.Analysis.matrixPartialIsometry_initial_complement_frame_zero
#print axioms ThomGame.Analysis.matrixPartialIsometry_final_complement_frame_zero
#print axioms ThomGame.Analysis.matrixPartialIsometry_stable_dimension_eq
#print axioms ThomGame.Analysis.matrixStableCompletionBlocks_initial
#print axioms ThomGame.Analysis.matrixStableCompletionBlocks_final
#print axioms ThomGame.Analysis.matrixStableCompletionUnitary_apply
#print axioms ThomGame.Analysis.matrixStableSourceFrame_initial
#print axioms ThomGame.Analysis.matrixStableTargetFrame_initial
#print axioms ThomGame.Analysis.matrixStableSourceFrame_eq_unitary
#print axioms ThomGame.Analysis.matrixStableFrames_overlap
#print axioms ThomGame.Analysis.matrixStableFrames_support_match
#print axioms ThomGame.Analysis.matrixStableFrames_adjoint_support_match
#print axioms ThomGame.Analysis.matrixFrame_final_projection
#print axioms ThomGame.Analysis.matrixFrameLift_projection
#print axioms ThomGame.Analysis.matrixStableFrames_source_corner
#print axioms ThomGame.Analysis.matrixStableFrames_target_corner
#print axioms ThomGame.Analysis.matrixStableFrames_common_support
#print axioms ThomGame.Analysis.matrixFrameLift_opNorm
#print axioms ThomGame.Analysis.matrixFrameCompression_opNorm_le
#print axioms ThomGame.Analysis.matrixStableCommonSupport_complement_trace
#print axioms ThomGame.Analysis.matrixFrame_complement_adjoint
#print axioms ThomGame.Analysis.matrixFrame_complement
#print axioms ThomGame.Analysis.matrixFrameLift_mul_complement
#print axioms ThomGame.Analysis.matrixFrameLift_complement_mul
#print axioms ThomGame.Analysis.mem_matrixFrameScalarAlgebra
#print axioms ThomGame.Analysis.matrixFrameScalarAlgebra_lift_mem
#print axioms ThomGame.Analysis.matrixFrameScalarAlgebra_compression_mem
#print axioms ThomGame.Analysis.matrixFrameScalarAlgebra_mono
#print axioms ThomGame.Analysis.matrixHSUnitBall_nonempty
#print axioms ThomGame.Analysis.matrixHSUnitBall_dist
#print axioms ThomGame.Analysis.matrixHSUnitBallHausdorff_nonneg
#print axioms ThomGame.Analysis.matrixHSUnitBall_hausdorffEDist_le
#print axioms ThomGame.Analysis.matrixHSUnitBallHausdorff_le
#print axioms ThomGame.Analysis.matrixCommonCompression_hausdorffEDist_bound
#print axioms ThomGame.Analysis.matrixCommonCompression_hausdorff_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSourceFrame_initial
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableTargetFrame_initial
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSourceFrame_eq_unitary
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableFrames_overlap
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableCorrected_inclusion
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableDim_eq
#print axioms ThomGame.Analysis.MatrixThomSpectralData.le_stableDim
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableDim_error
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_added_dimension_bounds
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableDim_ratio_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_target
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_projection
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_source_mem
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_target_mem
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_complement_trace
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_source_compression
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_target_compression
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_corners_eq
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_A_hausdorffEDist_finite
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_A_hausdorff_trace_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_A_hausdorff_bound
#print axioms ThomGame.Analysis.matrixThom_stable_dimension_ratio_tendsto
#print axioms ThomGame.Analysis.matrixThom_stable_complement_trace_tendsto
#print axioms ThomGame.Analysis.matrixThom_stable_A_hausdorff_tendsto
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_commutes_original_common
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_commutes_corrected_common
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_common_corner_agreement
#print axioms ThomGame.Analysis.matrixStarRepresentation_contraction
#print axioms ThomGame.Analysis.matrixStarRepresentation_contraction_lift
#print axioms ThomGame.Analysis.matrixStarRepresentation_unitBall_image
#print axioms ThomGame.Analysis.matrixPartialIsometry_corner_difference
#print axioms ThomGame.Analysis.matrixPartialIsometry_corner_distance
#print axioms ThomGame.Analysis.matrixFrames_intertwining_distance_bound
#print axioms ThomGame.Analysis.matrixStableFrames_distance_bound
#print axioms ThomGame.Analysis.matrixFrame_complement_trace
#print axioms ThomGame.Analysis.matrixFrame_compression_loss_sq
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSourceFrame_complement_trace
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableTargetFrame_complement_trace
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSourceFrame_compression_loss
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableTargetFrame_compression_loss
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_lift_distance
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_forward_contraction
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_reverse_contraction
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_hausdorffEDist_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_hausdorffEDist_finite
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_hausdorff_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_AB_hausdorff_bound
#print axioms ThomGame.Analysis.matrixThom_stable_B_hausdorff_tendsto
#print axioms ThomGame.Analysis.matrixThom_stable_AB_hausdorff_tendsto
#print axioms ThomGame.Analysis.rectHSNorm_antitone_denominator
#print axioms ThomGame.Analysis.hsNorm_le_rectHSNorm_of_dimension_le
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSupport_compression_loss
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_A_nearInclusions
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stable_B_nearInclusions
#print axioms ThomGame.Analysis.matrixInternal_eq_of_mutual_nearInclusion_errors
#print axioms ThomGame.Analysis.matrixThom_stable_A_internal_eq
#print axioms ThomGame.Analysis.matrixThom_stable_B_internal_eq
#print axioms ThomGame.Analysis.matrixInternalFiniteAlgebra_eq_of_quotient_eq
#print axioms ThomGame.Analysis.matrixThom_stable_A_finite_eq
#print axioms ThomGame.Analysis.matrixThom_stable_B_finite_eq
#print axioms ThomGame.Analysis.exists_matrixThomStableCorrection
#print axioms ThomGame.Analysis.exists_matrixThomStableHausdorffCorrection
#print axioms ThomGame.Analysis.rectHSNorm_rescale
#print axioms ThomGame.Analysis.matrixFrameLift_hsNorm_rescale
#print axioms ThomGame.Analysis.matrixFrameLift_hsNorm_recover
#print axioms ThomGame.Analysis.matrixProjection_compression_loss_opNorm
#print axioms ThomGame.Analysis.matrixFrame_compression_loss_opNorm
#print axioms ThomGame.Analysis.matrixFrame_complement_hsNorm
#print axioms ThomGame.Analysis.matrixFrameCompression_lift
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_apply
#print axioms ThomGame.Analysis.matrixFrameSequenceCompression_apply
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_mul
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_star
#print axioms ThomGame.Analysis.matrixFrameSequenceCompression_lift
#print axioms ThomGame.Analysis.matrixFrameSequenceCompression_one
#print axioms ThomGame.Analysis.matrixDimensionRatio_inverse_tendsto
#print axioms ThomGame.Analysis.matrixFrame_complement_hsNorm_tendsto
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_null
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_null_iff
#print axioms ThomGame.Analysis.matrixFrameSequence_compression_error_null
#print axioms ThomGame.Analysis.matrixFrameSequence_lift_compression_mk
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_one_mk
#print axioms ThomGame.Analysis.matrixFrameQuotientHom_mk
#print axioms ThomGame.Analysis.matrixFrameQuotientHom_injective
#print axioms ThomGame.Analysis.matrixFrameQuotientHom_surjective
#print axioms ThomGame.Analysis.matrixFrameQuotientEquiv_mk
#print axioms ThomGame.Analysis.matrixFrameQuotientEquiv_symm_mk
#print axioms ThomGame.Analysis.matrixFrameLift_normalizedTrace
#print axioms ThomGame.Analysis.matrixFrameSequenceLift_ultratrace
#print axioms ThomGame.Analysis.matrixFrameQuotientEquiv_trace
#print axioms ThomGame.Analysis.matrixFrameQuotientHom_internal_mem
#print axioms ThomGame.Analysis.matrixFrameInternalHom_bijective
#print axioms ThomGame.Analysis.matrixFrameInternalEquiv_val
#print axioms ThomGame.Analysis.matrixFrameQuotientHom_internal_map
#print axioms ThomGame.Analysis.matrixThomOriginalQuotientEquiv_internal_map
#print axioms ThomGame.Analysis.matrixThomOriginalQuotientEquiv_A_map
#print axioms ThomGame.Analysis.matrixThomOriginalQuotientEquiv_B_map
#print axioms ThomGame.Analysis.matrixThomOriginalQuotientEquiv_trace
#print axioms ThomGame.Analysis.matrixThom_stable_to_cut_ratio_tendsto
#print axioms ThomGame.Analysis.matrixThomCorrectedQuotientEquiv_internal_map
#print axioms ThomGame.Analysis.matrixThomCorrectedQuotientEquiv_trace
#print axioms ThomGame.Analysis.starAlgEquiv_mem_map_iff
#print axioms ThomGame.Analysis.matrixThomQuotientEquiv_stable
#print axioms ThomGame.Analysis.matrixThomQuotientEquiv_internal_iff
#print axioms ThomGame.Analysis.matrixThomQuotientEquiv_A_iff
#print axioms ThomGame.Analysis.matrixThomQuotientEquiv_B_iff
#print axioms ThomGame.Analysis.matrixThomQuotientEquiv_trace
#print axioms ThomGame.Analysis.exists_matrixThomTracialCorrection_of_small_error
#print axioms ThomGame.Analysis.matrixQuotientMk_eq_of_eventually_eq
#print axioms ThomGame.Analysis.matrixSequenceSetCut_of_mem
#print axioms ThomGame.Analysis.matrixSequenceSetCut_of_not_mem
#print axioms ThomGame.Analysis.matrixSequenceSetCut_mk
#print axioms ThomGame.Analysis.matrixInternalQuotient_le_of_eventually_le
#print axioms ThomGame.Analysis.matrixInternalQuotient_eq_of_eventually_eq
#print axioms ThomGame.Analysis.matrixSmallError_nonneg
#print axioms ThomGame.Analysis.matrixSmallError_lt_half
#print axioms ThomGame.Analysis.matrixSmallErrorAlgebra_eq
#print axioms ThomGame.Analysis.matrixSmallErrorAlgebra_mono
#print axioms ThomGame.Analysis.matrixSmallError_nearInclusion
#print axioms ThomGame.Analysis.matrixSmallError_eventually_lt_half
#print axioms ThomGame.Analysis.matrixSmallError_eventually_eq
#print axioms ThomGame.Analysis.matrixSmallError_tendsto
#print axioms ThomGame.Analysis.matrixSmallErrorAlgebra_eventually_eq
#print axioms ThomGame.Analysis.matrixSmallErrorAlgebra_internal_eq
#print axioms ThomGame.Analysis.exists_matrixThomModifiedData
#print axioms ThomGame.Analysis.matrixThomModified_cut_rank_pos
#print axioms ThomGame.Analysis.matrixThomModified_dimension_ratio_tendsto
#print axioms ThomGame.Analysis.matrixThomModified_support_trace_tendsto
#print axioms ThomGame.Analysis.matrixThomGeneralQuotientEquiv_A_iff
#print axioms ThomGame.Analysis.matrixThomGeneralQuotientEquiv_B_iff
#print axioms ThomGame.Analysis.matrixThomGeneralQuotientEquiv_trace
#print axioms ThomGame.Analysis.matrixThomModifiedCommonRepresentation_apply
#print axioms ThomGame.Analysis.matrixThomModifiedCommonRepresentation_range_le
#print axioms ThomGame.Analysis.matrixThomModified_common_corner_of_small
#print axioms ThomGame.Analysis.matrixThomModified_common_commutes_of_small
#print axioms ThomGame.Analysis.matrixThomModified_relative_eventually
#print axioms ThomGame.Analysis.matrixHSUnitBall_hausdorffEDist_finite
#print axioms ThomGame.Analysis.matrixThomModified_hausdorffEDist_finite
#print axioms ThomGame.Analysis.matrixThomModified_AB_hausdorff_tendsto
#print axioms ThomGame.Analysis.matrixThomModified_source_support_mem_eventually
#print axioms ThomGame.Analysis.exists_matrixThomGeneralTracialCorrection
#print axioms ThomGame.Analysis.cstarSelfAdjoint_eq_zero_of_isNilpotent
#print axioms ThomGame.Analysis.cstarArtinian_jacobson_eq_bot
#print axioms ThomGame.Analysis.cstarArtinian_isSemisimpleRing
#print axioms ThomGame.Analysis.matrixSubalgebra_jacobson_eq_bot
#print axioms ThomGame.Analysis.matrixSubalgebra_isSemisimpleRing
#print axioms ThomGame.Analysis.exists_matrixSubalgebra_algEquiv_pi_matrix
#print axioms ThomGame.Analysis.exists_matrixSubalgebraAlgebraicBlocks
#print axioms ThomGame.Analysis.matrixSubalgebraAlgebraicBlocks_finrank
#print axioms ThomGame.Analysis.matrixSubalgebraAlgebraicBlocks_sum_sq_le
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_equiv
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_mul_self
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_commutes
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_mul_of_ne
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_sum
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_ne_zero
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_projection
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSupport_star
#print axioms ThomGame.Analysis.matrixAlgebraicBlockInsert_equiv
#print axioms ThomGame.Analysis.matrixAlgebraicBlockInsert_injective
#print axioms ThomGame.Analysis.matrixAlgebraicBlockInsert_one
#print axioms ThomGame.Analysis.matrixAlgebraicBlockInsert_mul_of_ne
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_mul_same
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_mul_ne
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_diagonal_sum
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_ne_zero
#print axioms ThomGame.Analysis.matrixIdempotent_trace_eq_rank
#print axioms ThomGame.Analysis.matrixIdempotent_rank_eq_of_trace_eq
#print axioms ThomGame.Analysis.matrixIdempotent_rank_pos
#print axioms ThomGame.Analysis.matrixIdempotent_sum_rank
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_diagonal_idempotent
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_support_idempotent
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_diagonal_rank_eq
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_diagonal_rank
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_support_rank
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_dimension
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentationMultiplicity_pos
#print axioms ThomGame.Analysis.matrixAlgebraicOriginalMultiplicity_pos
#print axioms ThomGame.Analysis.matrixAlgebraicBlockSizes_sum_le
#print axioms ThomGame.Analysis.matrixAlgebraicBlockCount_le
#print axioms ThomGame.Analysis.rectangularMatrix_rank_add_le
#print axioms ThomGame.Analysis.rectangularMatrix_rank_sum_le
#print axioms ThomGame.Analysis.matrixAlgebraicIntertwiner_rank_le
#print axioms ThomGame.Analysis.matrixCommutingProducts_mul
#print axioms ThomGame.Analysis.matrixAlgebraicJointUnit_mul
#print axioms ThomGame.Analysis.matrixAlgebraicJoint_diagonal_idempotent
#print axioms ThomGame.Analysis.matrixAlgebraicJoint_diagonal_rank_eq
#print axioms ThomGame.Analysis.matrixAlgebraicJoint_diagonal_rank
#print axioms ThomGame.Analysis.matrixAlgebraicJointMultiplicity_row
#print axioms ThomGame.Analysis.matrixAlgebraicJointMultiplicity_swap
#print axioms ThomGame.Analysis.matrixAlgebraicJointMultiplicity_column
#print axioms ThomGame.Analysis.matrixAlgebraicJointMultiplicity_dimension
#print axioms ThomGame.Analysis.matrixAlgebraicMultiplicityDistance_nonneg
#print axioms ThomGame.Analysis.matrixAlgebraicMultiplicityDistance_eq
#print axioms ThomGame.Analysis.matrixAlgebraicMultiplicityDistance_le_intertwiner
#print axioms ThomGame.Analysis.matrixThom_source_multiplicity_bound
#print axioms ThomGame.Analysis.matrixThom_commutant_multiplicity_bound
#print axioms ThomGame.Analysis.matrixThom_intrinsic_multiplicity_sum_bound
#print axioms ThomGame.Analysis.exists_matrixThom_intrinsic_multiplicities
#print axioms ThomGame.Analysis.matrixThom_intrinsic_multiplicity_tendsto
#print axioms ThomGame.Analysis.exists_matrixThomModifiedMultiplicityBlocks
#print axioms ThomGame.Analysis.matrixThomModifiedMultiplicityDistance_nonneg
#print axioms ThomGame.Analysis.matrixThomModifiedMultiplicityDistance_bound
#print axioms ThomGame.Analysis.matrixThomModifiedMultiplicityDistance_tendsto
#print axioms ThomGame.Analysis.matrixSumGram_posSemidef
#print axioms ThomGame.Analysis.matrixSumGram_mulVec_eq_zero_iff
#print axioms ThomGame.Analysis.matrixSumGram_isUnit
#print axioms ThomGame.Analysis.matrixSumGram_posDef
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_total_diagonal_sum
#print axioms ThomGame.Analysis.matrixAlgebraicGram_star
#print axioms ThomGame.Analysis.matrixAlgebraicGram_eq_sumGram
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnits_common_kernel
#print axioms ThomGame.Analysis.matrixAlgebraicGram_posDef
#print axioms ThomGame.Analysis.matrixAlgebraicGram_isUnit
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_mul_ite
#print axioms ThomGame.Analysis.matrixAlgebraicBlockUnit_mul_other
#print axioms ThomGame.Analysis.matrixAlgebraicBlockGram_mul_same
#print axioms ThomGame.Analysis.matrixAlgebraicBlockGram_mul_other
#print axioms ThomGame.Analysis.matrixAlgebraicGram_mul_unit
#print axioms ThomGame.Analysis.matrixAlgebraicGram_intertwines_unit
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_val
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_star
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_mul_self
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_isUnit
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_support
#print axioms ThomGame.Analysis.matrixAlgebraicGramRootInv_star
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_inv_mul
#print axioms ThomGame.Analysis.matrixAlgebraicGramRoot_mul_inv
#print axioms ThomGame.Analysis.matrixAlgebraicGramConj_apply
#print axioms ThomGame.Analysis.matrixAlgebraicGramConj_unit_star
#print axioms ThomGame.Analysis.matrixAlgebraicGramConj_support
#print axioms ThomGame.Analysis.matrixAlgebraicBlockInsert_expansion
#print axioms ThomGame.Analysis.matrixAlgebraicBlocks_symm_expansion
#print axioms ThomGame.Analysis.matrixCorrectedBlockAlgEquiv_expansion
#print axioms ThomGame.Analysis.matrixCorrectedBlockAlgEquiv_star
#print axioms ThomGame.Analysis.matrixCorrectedBlockStarAlgEquiv_single
#print axioms ThomGame.Analysis.exists_matrixSubalgebra_starAlgEquiv_pi_matrix
#print axioms ThomGame.Analysis.exists_matrixSubalgebraStarBlocks
#print axioms ThomGame.Analysis.matrixStarBlockUnit_star
#print axioms ThomGame.Analysis.matrixStarBlockUnit_mul
#print axioms ThomGame.Analysis.matrixStarBlockUnit_mul_other
#print axioms ThomGame.Analysis.matrixStarBlockUnit_total_diagonal_sum
#print axioms ThomGame.Analysis.matrixStarRepresentationUnit_adjoint
#print axioms ThomGame.Analysis.matrixStarRepresentationUnit_diagonal_projection
#print axioms ThomGame.Analysis.matrixStarRepresentation_dimension
#print axioms ThomGame.Analysis.matrixStarRepresentationMultiplicity_pos
#print axioms ThomGame.Analysis.matrixStarBlockBaseFrame_initial
#print axioms ThomGame.Analysis.matrixStarBlockBaseFrame_final
#print axioms ThomGame.Analysis.matrixStarBlockBaseFrame_support
#print axioms ThomGame.Analysis.matrixStarBlockFrame_mul_adjoint
#print axioms ThomGame.Analysis.matrixStarBlockFrame_initial
#print axioms ThomGame.Analysis.matrixStarBlockFrames_final_sum
#print axioms ThomGame.Analysis.matrixStarRepresentationFrame_final
#print axioms ThomGame.Analysis.matrixStarBlockColumnIndex_card
#print axioms ThomGame.Analysis.matrixStarRepresentationBasis_final
#print axioms ThomGame.Analysis.matrixStarRepresentationBasis_initial
#print axioms ThomGame.Analysis.matrixStarRepresentationBasis_column
#print axioms ThomGame.Analysis.matrix_mul_single_column_expansion
#print axioms ThomGame.Analysis.matrixAlgebraicBlockInsert_left_mul
#print axioms ThomGame.Analysis.matrixStarBlockUnit_left_mul
#print axioms ThomGame.Analysis.matrixStarBlockFrame_action
#print axioms ThomGame.Analysis.matrixStandardBlockRepresentation_apply_eq
#print axioms ThomGame.Analysis.matrixStandardBlockRepresentation_apply_ne
#print axioms ThomGame.Analysis.matrix_mul_standardBlock_column
#print axioms ThomGame.Analysis.matrix_standardBlock_mul_row
#print axioms ThomGame.Analysis.matrixStarRepresentationStandard_apply
#print axioms ThomGame.Analysis.matrixStarRepresentationFrame_intertwines
#print axioms ThomGame.Analysis.matrixStarRepresentationBasis_intertwines
#print axioms ThomGame.Analysis.matrixStarRepresentationBasis_conjugates
#print axioms ThomGame.Analysis.matrixStarRepresentationBasis_recovers
#print axioms ThomGame.Analysis.exists_matrixStarRepresentation_unitary_blocks
#print axioms ThomGame.Analysis.exists_matrixSubalgebra_unitary_blocks
#print axioms ThomGame.Analysis.matrixComplementaryBlockRepresentation_apply_eq
#print axioms ThomGame.Analysis.matrixComplementaryBlockRepresentation_apply_ne
#print axioms ThomGame.Analysis.matrixStandard_complementary_blocks_commute
#print axioms ThomGame.Analysis.matrixStandardBlockCommutant_off_block
#print axioms ThomGame.Analysis.matrixStandardBlockCommutant_off_diagonal
#print axioms ThomGame.Analysis.matrixStandardBlockCommutant_diagonal_eq
#print axioms ThomGame.Analysis.matrixStandardBlockCommutant_iff
#print axioms ThomGame.Analysis.matrixStarRepresentationCoordinates_apply
#print axioms ThomGame.Analysis.matrixStarRepresentationCoordinates_representation
#print axioms ThomGame.Analysis.matrixStarRepresentationCoordinates_blocks
#print axioms ThomGame.Analysis.matrixStarRepresentationBlocks_equiv
#print axioms ThomGame.Analysis.matrixStarRepresentation_range_eq_blocks
#print axioms ThomGame.Analysis.matrixStarRepresentationCoordinates_complementary
#print axioms ThomGame.Analysis.matrixStarRepresentation_mem_commutant_iff
#print axioms ThomGame.Analysis.matrixStarRepresentation_commutant_eq
#print axioms ThomGame.Analysis.matrixSubalgebra_subtype_range
#print axioms ThomGame.Analysis.matrixSubalgebra_eq_standard_blocks
#print axioms ThomGame.Analysis.matrixSubalgebra_eq_complementary_blocks
#print axioms ThomGame.Analysis.matrixThom_star_block_algebras
#print axioms ThomGame.Analysis.matrixThom_star_multiplicity_bound
#print axioms ThomGame.Analysis.exists_matrixThom_star_multiplicities
#print axioms ThomGame.Analysis.matrixThom_star_multiplicity_tendsto
#print axioms ThomGame.Analysis.exists_matrixThomModifiedStarBlocks
#print axioms ThomGame.Analysis.matrixThomModifiedStar_corrected_algebras
#print axioms ThomGame.Analysis.matrixThomModifiedStar_original_algebras_eventually
#print axioms ThomGame.Analysis.matrixThomModifiedStar_multiplicity_tendsto

#print axioms ThomGame.Analysis.exists_matrixBlock_trim
#print axioms ThomGame.Analysis.exists_matrixBlocks_trim_bounded
#print axioms ThomGame.Analysis.matrixBlock_min_le_sqrt_total
#print axioms ThomGame.Analysis.exists_matrixBlocks_trim
#print axioms ThomGame.Analysis.exists_matrixBlocks_trim_relative
#print axioms ThomGame.Analysis.matrixCanonicalCornerFrame_initial
#print axioms ThomGame.Analysis.matrixFrame_final_rank
#print axioms ThomGame.Analysis.matrixCanonicalCornerFrame_rank
#print axioms ThomGame.Analysis.matrixDimensionRatio_max_target_tendsto
#print axioms ThomGame.Analysis.matrixDimensionRatio_max_source_tendsto
#print axioms ThomGame.Analysis.matrixCanonicalDimensionEquiv_to_common
#print axioms ThomGame.Analysis.matrixCanonicalDimensionEquiv_mk
#print axioms ThomGame.Analysis.matrixCanonicalDimensionEquiv_trace
#print axioms ThomGame.Analysis.exists_matrixCanonicalDimensionPreimage
#print axioms ThomGame.Analysis.matrixCanonicalDimension_internal_iff
#print axioms ThomGame.Analysis.exists_matrixCanonicalDimensionStability
#print axioms ThomGame.Analysis.matrixDimensionCut_compression_loss
#print axioms ThomGame.Analysis.matrixDimensionCut_forward_approximation
#print axioms ThomGame.Analysis.matrixDimensionCut_reverse_approximation
#print axioms ThomGame.Analysis.matrixDimensionCut_hausdorffEDist_bound
#print axioms ThomGame.Analysis.matrixDimensionCut_hausdorff_bound
#print axioms ThomGame.Analysis.matrixDimensionCut_nearInclusions
#print axioms ThomGame.Analysis.matrixDimensionCut_internal_eq
#print axioms ThomGame.Analysis.matrixDimensionCut_slack_ratio_bound
#print axioms ThomGame.Analysis.matrixDimensionCut_slack_ratio_tendsto
#print axioms ThomGame.Analysis.matrixDimensionCut_complement_trace_tendsto
#print axioms ThomGame.Analysis.matrixDimensionCut_hausdorff_tendsto
#print axioms ThomGame.Analysis.exists_matrixDimensionCutTarget
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.fullFrame_initial
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.fullFrame_lift
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.fullFrame_complement_trace
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.fullFrame_lift_mem
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.fullFrame_compression_mem
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.fullFrame_compression_loss
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.forward_approximation
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.reverse_approximation
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.unitBall_approximations
#print axioms ThomGame.Analysis.MatrixDimensionCutTarget.hausdorff_bound
#print axioms ThomGame.Analysis.matrixDimensionCutTarget_error_tendsto
#print axioms ThomGame.Analysis.matrixDimensionCutTarget_hausdorff_tendsto
#print axioms ThomGame.Analysis.matrixDimensionCutTarget_internal_eq
#print axioms ThomGame.Analysis.matrixDimensionCutTarget_canonical_map
#print axioms ThomGame.Analysis.exists_matrixDimensionDecreasing_canonical_algebras
#print axioms ThomGame.Analysis.matrixFrame_unitary_initial
#print axioms ThomGame.Analysis.exists_matrixFrame_move_to_corner_near
#print axioms ThomGame.Analysis.matrixFrame_composition_initial
#print axioms ThomGame.Analysis.matrixFrameLift_composition
#print axioms ThomGame.Analysis.matrixFrameCompression_composition
#print axioms ThomGame.Analysis.matrixNestedFrameScalar_lift_mem
#print axioms ThomGame.Analysis.matrixNestedFrameScalar_compression_mem
#print axioms ThomGame.Analysis.mem_matrixProjectionCommutingPart
#print axioms ThomGame.Analysis.matrixProductCornerFrame_left_support
#print axioms ThomGame.Analysis.matrixProductCornerFrame_adjoint_support
#print axioms ThomGame.Analysis.matrixProductCornerFrame_reducing
#print axioms ThomGame.Analysis.matrixProductCornerRepresentation_apply
#print axioms ThomGame.Analysis.matrixProductCorner_compression_mem
#print axioms ThomGame.Analysis.matrixProductCorner_contraction_lift
#print axioms ThomGame.Analysis.matrixProductCorner_unitBall_compression_image
#print axioms ThomGame.Analysis.rectHSNorm_sub_triangle
#print axioms ThomGame.Analysis.rectHSNorm_sub_triangle_three
#print axioms ThomGame.Analysis.exists_matrixUnitary_projection_conjugacy_near
#print axioms ThomGame.Analysis.matrixInitialProjection_isStarProjection
#print axioms ThomGame.Analysis.matrixStandardBlockRepresentation_diagonal
#print axioms ThomGame.Analysis.matrixComplementaryBlockRepresentation_diagonal
#print axioms ThomGame.Analysis.matrixRetainedBlockIndex_card
#print axioms ThomGame.Analysis.matrixStandardBlockCuts_product_rank
#print axioms ThomGame.Analysis.matrixInitialProjection_family
#print axioms ThomGame.Analysis.matrixStarRepresentationCoordinates_rank
#print axioms ThomGame.Analysis.matrixSubalgebraFactorCut_projection
#print axioms ThomGame.Analysis.matrixSubalgebraMultiplicityCut_projection
#print axioms ThomGame.Analysis.matrixSubalgebraFactorCut_mem
#print axioms ThomGame.Analysis.matrixSubalgebraMultiplicityCut_mem
#print axioms ThomGame.Analysis.matrixSubalgebraCuts_commute
#print axioms ThomGame.Analysis.matrixSubalgebraCuts_product_projection
#print axioms ThomGame.Analysis.matrixSubalgebraCuts_product_rank
#print axioms ThomGame.Analysis.exists_matrixSubalgebra_dimension_projections
#print axioms ThomGame.Analysis.exists_matrixSubalgebraDimensionCut
#print axioms ThomGame.Analysis.matrixSubalgebraDimensionCut_size_le
#print axioms ThomGame.Analysis.matrixSubalgebraDimensionCut_unitBall_image
#print axioms ThomGame.Analysis.matrixSubalgebraDimensionCut_complement_trace
#print axioms ThomGame.Analysis.matrixHSUnitBallHausdorff_bound_rescale
#print axioms ThomGame.Analysis.matrixUnitary_conjugation_opNorm
#print axioms ThomGame.Analysis.matrixUnitary_conjugation_distance

#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_unit_trace
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_trace
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_idempotent_rank
#print axioms ThomGame.Analysis.matrixAlgebraicRepresentation_block_cut_rank
#print axioms ThomGame.Analysis.matrixInclusionBlockRepresentation_apply
#print axioms ThomGame.Analysis.matrixInclusionMultiplicity_row
#print axioms ThomGame.Analysis.matrixInclusionMultiplicity_column
#print axioms ThomGame.Analysis.matrixInclusionMultiplicity_size_bound
#print axioms ThomGame.Analysis.matrixInclusionMultiplicity_multiplicity_bound
#print axioms ThomGame.Analysis.matrixStarBlockSupport_projection
#print axioms ThomGame.Analysis.matrixStarBlockSupport_mem
#print axioms ThomGame.Analysis.matrixStarBlockSupport_commutes
#print axioms ThomGame.Analysis.matrixStarBlockSupport_orthogonal
#print axioms ThomGame.Analysis.matrixStarBlockSupport_sum
#print axioms ThomGame.Analysis.matrixStarBlockSupport_rank
#print axioms ThomGame.Analysis.matrixStarBlockSupport_trace
#print axioms ThomGame.Analysis.matrixStarBlockScalar_mem
#print axioms ThomGame.Analysis.matrixStarBlockScalar_commutes
#print axioms ThomGame.Analysis.matrixStarBlockScalar_nonneg
#print axioms ThomGame.Analysis.matrixStarBlockScalar_one
#print axioms ThomGame.Analysis.matrixStarBlockScalar_mul
#print axioms ThomGame.Analysis.matrixStarBlockScalar_inverse
#print axioms ThomGame.Analysis.matrixStarBlockScalar_isUnit
#print axioms ThomGame.Analysis.matrixStarBlockScalar_block
#print axioms ThomGame.Analysis.matrixInclusion_supports_commute
#print axioms ThomGame.Analysis.matrixInclusionCell_projection
#print axioms ThomGame.Analysis.matrixInclusionCell_sum
#print axioms ThomGame.Analysis.matrixInclusionCell_rank
#print axioms ThomGame.Analysis.matrixInclusionCell_zero_iff
#print axioms ThomGame.Analysis.matrixInclusionCell_trace
#print axioms ThomGame.Analysis.matrixSubalgebraScale_coefficient_pos
#print axioms ThomGame.Analysis.matrixSubalgebraScale_mem
#print axioms ThomGame.Analysis.matrixSubalgebraScale_commutes
#print axioms ThomGame.Analysis.matrixSubalgebraScale_nonneg
#print axioms ThomGame.Analysis.matrixSubalgebraScale_isUnit
#print axioms ThomGame.Analysis.matrixSubalgebraScale_posDef
#print axioms ThomGame.Analysis.matrixSubalgebraScale_inverse
#print axioms ThomGame.Analysis.matrixSubalgebraScale_inverse_mem
#print axioms ThomGame.Analysis.matrixSubalgebraScale_inverse_nonneg
#print axioms ThomGame.Analysis.matrixSubalgebraScale_inverse_commutes
#print axioms ThomGame.Analysis.matrixSubalgebraScale_mul_inverse
#print axioms ThomGame.Analysis.matrixSubalgebraScale_inverse_mul
#print axioms ThomGame.Analysis.matrixInclusionScaleCoefficient_pos
#print axioms ThomGame.Analysis.matrixInclusionScaleCoefficient_sq_lower
#print axioms ThomGame.Analysis.matrixInclusionScaleCoefficient_one_le
#print axioms ThomGame.Analysis.matrixInclusionBlockScalars_product
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_expansion
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_one_le
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_nonneg
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_inverse
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_inverse_expansion
#print axioms ThomGame.Analysis.matrixTraceReal_ofReal_smul
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_inverse_nonneg
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_inverse_le_one
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_inverse_trace
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_trace_defect_nonneg
#print axioms ThomGame.Analysis.matrixStarRepresentation_unit_trace
#print axioms ThomGame.Analysis.matrixStarRepresentation_unit_pairing
#print axioms ThomGame.Analysis.matrixStarRepresentation_trace
#print axioms ThomGame.Analysis.matrixStarRepresentation_unit_hsNorm_sq
#print axioms ThomGame.Analysis.matrixStarRepresentation_hsNorm_sq
#print axioms ThomGame.Analysis.matrixTraceProjection_unnormalized_pairing
#print axioms ThomGame.Analysis.matrixBlockExpectation_entry
#print axioms ThomGame.Analysis.matrixBlockExpectation_hsNorm_sq
#print axioms ThomGame.Analysis.matrixInclusion_unit_pairing
#print axioms ThomGame.Analysis.matrixInclusion_expectation_unit_entry
#print axioms ThomGame.Analysis.matrixInclusion_expectation_entry_energy
#print axioms ThomGame.Analysis.matrixInclusion_expectation_block_energy
#print axioms ThomGame.Analysis.matrixInclusion_expectation_unit_energy
#print axioms ThomGame.Analysis.matrixInclusion_expectation_energy_scale_trace
#print axioms ThomGame.Analysis.matrixBlockUnitSandwich_mul_left
#print axioms ThomGame.Analysis.matrixBlockUnitSandwich_mul_right
#print axioms ThomGame.Analysis.matrixBlockUnitSandwich_mul_left_other
#print axioms ThomGame.Analysis.matrixBlockUnitSandwich_mul_right_other
#print axioms ThomGame.Analysis.matrixBlockCommutantAverage_commutes_unit
#print axioms ThomGame.Analysis.matrixBlockCommutantAverage_commutes
#print axioms ThomGame.Analysis.matrixBlockCommutantAverage_mem
#print axioms ThomGame.Analysis.matrixBlockUnitSandwich_trace_pairing
#print axioms ThomGame.Analysis.matrixBlockCommutantAverage_trace_pairing
#print axioms ThomGame.Analysis.matrixBlockCommutantAverage_eq_expectation
#print axioms ThomGame.Analysis.matrixBlockCommutantAverage_range_overlap
#print axioms ThomGame.Analysis.matrixStinespring_commutant_overlap_scale
#print axioms ThomGame.Analysis.matrixStinespring_commutant_variance_scale
#print axioms ThomGame.Analysis.rectHSNorm_commutator_contraction_le
#print axioms ThomGame.Analysis.matrixTraceProjection_pythagoras
#print axioms ThomGame.Analysis.matrixStinespring_expectation_commutator_sq
#print axioms ThomGame.Analysis.matrixReverseInclusion_scale_sq
#print axioms ThomGame.Analysis.matrixReverseInclusion_scale
#print axioms ThomGame.Analysis.matrixReverseInclusion_scale_error
#print axioms ThomGame.Analysis.matrixThom_lemma_4_1
#print axioms ThomGame.Analysis.matrixReverseInclusion_scale_near

#print axioms ThomGame.Analysis.boundedScaleScalar_pos
#print axioms ThomGame.Analysis.boundedScaleScalar_le_one
#print axioms ThomGame.Analysis.boundedScaleScalar_lt_one
#print axioms ThomGame.Analysis.boundedScaleScalar_zero
#print axioms ThomGame.Analysis.boundedScaleScalar_le_half
#print axioms ThomGame.Analysis.boundedScaleScalar_strictAnti
#print axioms ThomGame.Analysis.boundedScaleScalar_monotone
#print axioms ThomGame.Analysis.boundedScaleScalar_continuousOn
#print axioms ThomGame.Analysis.boundedScaleScalar_sub
#print axioms ThomGame.Analysis.boundedScaleScalar_abs_sub_le_ratio
#print axioms ThomGame.Analysis.boundedScaleScalar_abs_sub_sq_le_ratio
#print axioms ThomGame.Analysis.weightedBoundedScale_zero
#print axioms ThomGame.Analysis.weightedBoundedScale_continuousOn
#print axioms ThomGame.Analysis.weightedBoundedScale_strictAnti
#print axioms ThomGame.Analysis.exists_unique_weightedScaleMedian
#print axioms ThomGame.Analysis.weightedScaleMedian_pos
#print axioms ThomGame.Analysis.weightedScaleMedian_mean
#print axioms ThomGame.Analysis.matrixStarBlockScalarElement_equiv
#print axioms ThomGame.Analysis.matrixStarBlockSupport_diagonal_sum
#print axioms ThomGame.Analysis.matrixStarBlockScalar_const
#print axioms ThomGame.Analysis.matrixStarBlockScalar_sub
#print axioms ThomGame.Analysis.matrixStarBlockScalar_mono
#print axioms ThomGame.Analysis.matrixStarBlockScalar_posDef
#print axioms ThomGame.Analysis.matrixInclusionConditionalWeight_nonneg
#print axioms ThomGame.Analysis.matrixInclusionConditionalWeight_sum
#print axioms ThomGame.Analysis.matrixInclusion_support_trace_pairing
#print axioms ThomGame.Analysis.matrixInclusion_support_expectation
#print axioms ThomGame.Analysis.matrixInclusion_cell_expectation
#print axioms ThomGame.Analysis.matrixInclusionCell_mul
#print axioms ThomGame.Analysis.matrixInclusionCell_orthogonal
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_sum
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_one
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_add
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_sub
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_mul
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_inverse
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_isUnit
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_source
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_target
#print axioms ThomGame.Analysis.matrixInclusionCell_row_sum
#print axioms ThomGame.Analysis.matrixInclusionCell_column_sum
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_nonneg
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_mono
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_posDef
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_mem
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_commutes
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_star
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_trace
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_hsNorm_sq
#print axioms ThomGame.Analysis.matrixBoundedScale_cellFormula
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusionFormula
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusion_posDef
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusion_one_sub_posDef
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusion_mem
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusion_commutes
#print axioms ThomGame.Analysis.matrixInclusionCellScalar_expectation
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusion_expectation
#print axioms ThomGame.Analysis.matrixConditionalScaleMedianCoefficients_pos
#print axioms ThomGame.Analysis.matrixConditionalScaleMedianCoefficients_mean
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_posDef
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_mem
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_commutes
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_bounded_posDef
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_bounded_one_sub_posDef
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_bounded_mem
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_bounded_commutes
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_bounded_norm
#print axioms ThomGame.Analysis.matrixConditionalScaleMedian_expectation
#print axioms ThomGame.Analysis.matrixBoundedScale_cellPerturbation_sq
#print axioms ThomGame.Analysis.matrixBoundedScale_targetPerturbation_sq
#print axioms ThomGame.Analysis.matrixBoundedScale_targetPerturbation_rank_bound
#print axioms ThomGame.Analysis.matrixSubalgebraConditionalMedian_posDef
#print axioms ThomGame.Analysis.matrixSubalgebraConditionalMedian_center
#print axioms ThomGame.Analysis.matrixSubalgebraConditionalMedian_bounded_spec
#print axioms ThomGame.Analysis.matrixSubalgebraConditionalMedian_expectation
#print axioms ThomGame.Analysis.matrixSubalgebraConditionalMedian_corner_expectation
#print axioms ThomGame.Analysis.exists_matrixSubalgebraConditionalMedian
#print axioms ThomGame.Analysis.matrixBoundedScale_sizeChange
#print axioms ThomGame.Analysis.matrixBoundedScale_multiplicityChange
#print axioms ThomGame.Analysis.matrixNonsingular_inverse_intertwines
#print axioms ThomGame.Analysis.matrixBoundedScale_intertwines
#print axioms ThomGame.Analysis.matrixBoundedScale_intertwines_posDef
#print axioms ThomGame.Analysis.matrixAlgHom_map_nonsing_inv
#print axioms ThomGame.Analysis.matrixBoundedScale_map
#print axioms ThomGame.Analysis.matrixBoundedScale_sizeChange_tendsto
#print axioms ThomGame.Analysis.matrixBoundedScale_multiplicityChange_tendsto

-- Actual retained blocks and corrected bounded scales.
#print axioms ThomGame.Analysis.matrixStandardBlockRepresentation_eq_iff
#print axioms ThomGame.Analysis.matrixStarRepresentation_eq_iff
#print axioms ThomGame.Analysis.matrixStarRepresentationBlocks_eq_iff
#print axioms ThomGame.Analysis.matrixStarRepresentationComplementary_injective
#print axioms ThomGame.Analysis.matrixStarRepresentationComplementary_eq_iff
#print axioms ThomGame.Analysis.matrixRetainedBlockCoordinates_map
#print axioms ThomGame.Analysis.matrixRetainedBlockCoordinatesHom_bijective
#print axioms ThomGame.Analysis.matrixRetainedBlockRangeEquiv_map
#print axioms ThomGame.Analysis.matrixRetainedBlockLabel_injective
#print axioms ThomGame.Analysis.matrixRetainedBlockLabel_mem
#print axioms ThomGame.Analysis.matrixRetainedBlockRangeBlocks_equiv_map
#print axioms ThomGame.Analysis.matrixRetainedBlockRangeBlocks_symm_single
#print axioms ThomGame.Analysis.matrixRetainedBlockRangeBlocks_unit
#print axioms ThomGame.Analysis.matrixRetainedBlockRangeBlocks_support
#print axioms ThomGame.Analysis.matrixRetainedBlockRangeBlocks_scalar
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedLabel_pos
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedBlocks_unit
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedBlocks_multiplicity
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedBlocks_support
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedBlocks_scalar
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedBlocks_scale
#print axioms ThomGame.Analysis.matrixStandard_complementary_support_eq
#print axioms ThomGame.Analysis.matrixStarRepresentationComplementary_support
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedComplementary_support
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedComplementary_multiplicity
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedComplementary_scalar
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedComplementary_scale
#print axioms ThomGame.Analysis.matrixRetainedBlock_sum_le
#print axioms ThomGame.Analysis.matrixStarRepresentationRetained_scaleChange
#print axioms ThomGame.Analysis.matrixStarRepresentationRetainedComplementary_scaleChange
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedSourceScale_formula
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedTargetScale_formula
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedSourceScale_mem
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedTargetScale_mem
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedSourceScale_posDef
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedTargetScale_posDef
#print axioms ThomGame.Analysis.MatrixThomSpectralData.commonRetainedRange_le_source
#print axioms ThomGame.Analysis.MatrixThomSpectralData.commonRetainedRange_le_target
#print axioms ThomGame.Analysis.MatrixThomSpectralData.commonPositiveScalar_retained
#print axioms ThomGame.Analysis.MatrixThomSpectralData.commonPositiveScalar_posDef
#print axioms ThomGame.Analysis.matrixThom_retainedSourceScale_error
#print axioms ThomGame.Analysis.matrixThom_retainedTargetScale_error
#print axioms ThomGame.Analysis.matrixThom_retainedScale_error_sum
#print axioms ThomGame.Analysis.matrixThom_retainedSourceScale_tendsto
#print axioms ThomGame.Analysis.matrixThom_retainedTargetScale_tendsto
#print axioms ThomGame.Analysis.matrixThom_retainedScale_tendsto

-- Actual conditional median and simultaneous stable unitary transport.
#print axioms ThomGame.Analysis.matrixBoundedScale_inclusion_norm
#print axioms ThomGame.Analysis.matrixSubalgebraBoundedScale_map
#print axioms ThomGame.Analysis.MatrixThomSpectralData.rawSourceScale_posDef
#print axioms ThomGame.Analysis.MatrixThomSpectralData.rawTargetScale_posDef
#print axioms ThomGame.Analysis.matrixSubalgebraBoundedScaleElement_norm
#print axioms ThomGame.Analysis.MatrixThomSpectralData.sourceBoundedScale_map
#print axioms ThomGame.Analysis.MatrixThomSpectralData.sourceRawBoundedScale_stable_distance
#print axioms ThomGame.Analysis.matrixSubalgebraComplementaryScale_coefficient_pos
#print axioms ThomGame.Analysis.matrixSubalgebraComplementaryScale_posDef
#print axioms ThomGame.Analysis.matrixSubalgebraComplementaryScale_eq_scale
#print axioms ThomGame.Analysis.matrixSubalgebraComplementaryScale_mem
#print axioms ThomGame.Analysis.matrixSubalgebraComplementaryScale_bounded_norm
#print axioms ThomGame.Analysis.MatrixThomSpectralData.targetRawBoundedScale_intertwines
#print axioms ThomGame.Analysis.MatrixThomSpectralData.targetRawBoundedScale_norm
#print axioms ThomGame.Analysis.MatrixThomSpectralData.targetRawBoundedScale_stable_distance
#print axioms ThomGame.Analysis.matrixFrameLift_distance_triangle
#print axioms ThomGame.Analysis.MatrixThomSpectralData.sourceBoundedScale_stable_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.targetBoundedScale_stable_bound
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableSourceFrameLift_unitary
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableUnitary_transport_norm
#print axioms ThomGame.Analysis.MatrixThomSpectralData.stableUnitary_transport_normalized_le
#print axioms ThomGame.Analysis.matrixThom_sourceBoundedScale_stable_tendsto
#print axioms ThomGame.Analysis.matrixThom_targetBoundedScale_stable_tendsto
#print axioms ThomGame.Analysis.matrixThom_boundedScale_common_unitary_tendsto
#print axioms ThomGame.Analysis.matrixStarBlocksTransport_unit
#print axioms ThomGame.Analysis.matrixStarBlocksTransport_scalar
#print axioms ThomGame.Analysis.matrixStarBlocksTransport_multiplicity
#print axioms ThomGame.Analysis.matrixStarBlocksTransport_scale
#print axioms ThomGame.Analysis.matrixStarSubalgebraEquivOfEq_coe
#print axioms ThomGame.Analysis.matrixSubalgebraComplementaryBlocks_scale
#print axioms ThomGame.Analysis.matrixUnitaryPullbackHom_bijective
#print axioms ThomGame.Analysis.matrixUnitaryPullbackEquiv_coe
#print axioms ThomGame.Analysis.matrixUnitaryPullbackEquiv_trace
#print axioms ThomGame.Analysis.matrixUnitaryPullbackBlocks_multiplicity
#print axioms ThomGame.Analysis.matrixUnitaryPullbackBlocks_scale
#print axioms ThomGame.Analysis.matrixUnitaryPullbackBlocks_boundedScale
#print axioms ThomGame.Analysis.matrixUnitaryPullback_contains_common
#print axioms ThomGame.Analysis.matrixAnchoredScaleCoefficients_pos
#print axioms ThomGame.Analysis.matrixAnchoredBoundedScale_eq_median
#print axioms ThomGame.Analysis.matrixAnchoredBoundedScale_spec
#print axioms ThomGame.Analysis.matrixAnchoredBoundedScale_expectation
#print axioms ThomGame.Analysis.matrixAnchoredBoundedScale_pullback
#print axioms ThomGame.Analysis.matrixThom_anchoredScale_common_unitary_tendsto

-- Actual order, quantitative concentration and anchored no drift.
#print axioms ThomGame.Analysis.matrixCommute_nonsing_inv_right
#print axioms ThomGame.Analysis.matrixCommute_posDef_mul
#print axioms ThomGame.Analysis.matrixPosDef_inverse_antitone
#print axioms ThomGame.Analysis.matrixBoundedScale_one_sub
#print axioms ThomGame.Analysis.matrixBoundedScale_posDef
#print axioms ThomGame.Analysis.matrixBoundedScale_one_sub_posDef
#print axioms ThomGame.Analysis.matrixBoundedScale_mono
#print axioms ThomGame.Analysis.matrixBoundedScale_norm_le_one
#print axioms ThomGame.Analysis.matrixSubalgebraScale_le_of_inclusion
#print axioms ThomGame.Analysis.matrixInclusionBoundedScale_order
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedRange_le
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedScale_le
#print axioms ThomGame.Analysis.MatrixThomSpectralData.commonPositiveScalar_mem_retainedSource
#print axioms ThomGame.Analysis.matrixThom_boundedScale_order
#print axioms ThomGame.Analysis.matrixBoundedScale_mul_sum
#print axioms ThomGame.Analysis.matrixBoundedScale_one_sub_mul_sum
#print axioms ThomGame.Analysis.matrixBoundedScale_ratio_defect_identity
#print axioms ThomGame.Analysis.matrixRatioDefect_center_identity
#print axioms ThomGame.Analysis.matrixRatioDefect_center_bound
#print axioms ThomGame.Analysis.matrixTraceReal_self_le_rectHSNorm
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_defect_norm
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_defect_trace
#print axioms ThomGame.Analysis.matrixReverseInclusion_center_error
#print axioms ThomGame.Analysis.matrixReverseInclusion_center_near
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_defect_norm_tendsto
#print axioms ThomGame.Analysis.matrixInclusionScaleRatio_defect_trace_tendsto
#print axioms ThomGame.Analysis.matrixReverseInclusion_center_tendsto
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedScaleRatio_one_le
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedScaleRatio_inverse
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedScaleRatio_trace_defect_nonneg
#print axioms ThomGame.Analysis.MatrixThomSpectralData.retainedScaleConcentration_nonneg
#print axioms ThomGame.Analysis.matrixThom_retainedScaleRatio_defect_norm
#print axioms ThomGame.Analysis.matrixThom_retainedScaleRatio_defect_trace
#print axioms ThomGame.Analysis.matrixThom_reverseInclusion_center_error
#print axioms ThomGame.Analysis.matrixThom_reverseInclusion_center_near
#print axioms ThomGame.Analysis.matrixThom_retainedScaleRatio_defect_trace_tendsto
#print axioms ThomGame.Analysis.matrixThom_reverseInclusion_center_tendsto
#print axioms ThomGame.Analysis.matrixPositiveContraction_hsNorm_sq_le_trace
#print axioms ThomGame.Analysis.matrixFrameLift_nonneg
#print axioms ThomGame.Analysis.matrixFrameLift_mono
#print axioms ThomGame.Analysis.matrixFrameLift_le_one
#print axioms ThomGame.Analysis.matrixOrdered_equalTrace_distance
#print axioms ThomGame.Analysis.matrixFrame_ordered_equalTrace_distance
#print axioms ThomGame.Analysis.matrixThom_ordered_transport_tendsto
#print axioms ThomGame.Analysis.matrixThom_anchoredScale_conjugation_tendsto
#print axioms ThomGame.Analysis.matrixThom_anchoredScale_commutator_tendsto

-- Actual anchor, concentration, reverse transfer, and full Thom Theorem 4.2.
#print axioms ThomGame.Analysis.matrixQuotientMk_mem_relativeCommutant_of_tendsto
#print axioms ThomGame.Analysis.matrixQuotientAnchor_scalar
#print axioms ThomGame.Analysis.matrixQuotientAnchor_scalar_tendsto
#print axioms ThomGame.Analysis.matrixAnchoredScaleSequence_mem
#print axioms ThomGame.Analysis.matrixAnchoredScaleSequence_expectation
#print axioms ThomGame.Analysis.matrixAnchoredScaleSequence_mem_internal
#print axioms ThomGame.Analysis.matrixInternal_unitaryPullback_eq
#print axioms ThomGame.Analysis.matrixThom_anchoredScale_half_of_corrections
#print axioms ThomGame.Analysis.matrixThom_anchoredScale_half_of_internal_inclusions
#print axioms ThomGame.Analysis.matrixThom_anchoredScale_half
#print axioms ThomGame.Analysis.matrixFrame_scalar_concentration_transfer
#print axioms ThomGame.Analysis.matrixFrame_scalar_concentration_transfer_eventually
#print axioms ThomGame.Analysis.hsNorm_unitaryPullback_sub_scalar
#print axioms ThomGame.Analysis.matrixThom_scalar_transport_tendsto
#print axioms ThomGame.Analysis.matrixThom_stable_to_cut_ratio_tendsto_general
#print axioms ThomGame.Analysis.matrixThom_scalar_transport_tendsto_general
#print axioms ThomGame.Analysis.matrixThom_correctedScale_concentration
#print axioms ThomGame.Analysis.matrixNearInclusion_contraction
#print axioms ThomGame.Analysis.rectHSNorm_dimension_rescale
#print axioms ThomGame.Analysis.MatrixThomSpectralData.reverse_nearInclusion_transfer
#print axioms ThomGame.Analysis.matrixThom_reverse_nearInclusion_tendsto
#print axioms ThomGame.Analysis.matrixThom_reverseInclusion_center_near_general
#print axioms ThomGame.Analysis.matrixThom_reverseInclusion_original_tendsto
#print axioms ThomGame.Analysis.matrixThom_theorem_4_2_of_internal_inclusions
#print axioms ThomGame.Analysis.matrixThom_theorem_4_2
#print axioms ThomGame.Analysis.matrixInternalFinite_unitaryPullback_eq
#print axioms ThomGame.Analysis.matrixThom_finite_theorem_4_2_of_internal_inclusions
#print axioms ThomGame.Analysis.matrixThom_finite_theorem_4_2

-- Internal alignment, arbitrary homomorphism normalization, and actual Q/H application.
#print axioms ThomGame.Analysis.starAlgHomUnitary_val
#print axioms ThomGame.Analysis.unitaryRangeCommutant_mem_iff
#print axioms ThomGame.Analysis.starAlgEquiv_commute_iff
#print axioms ThomGame.Analysis.starAlgEquiv_unitaryPullback_apply
#print axioms ThomGame.Analysis.starAlgEquiv_unitaryCommutant_mem_iff
#print axioms ThomGame.Analysis.exists_matrixInternal_nested_realization
#print axioms ThomGame.Analysis.matrixThom_theorem_4_2_of_unitaries
#print axioms ThomGame.Analysis.matrixThom_internal_normalization
#print axioms ThomGame.Analysis.unitaryRepresentationCommutant_mem_iff
#print axioms ThomGame.Analysis.unitaryRepresentationCommutant_generator_anchor
#print axioms ThomGame.Analysis.unitaryRepresentationCommutant_compressor_inclusion
#print axioms ThomGame.Analysis.unitaryRepresentationCommutant_unitary_mem_iff
#print axioms ThomGame.Analysis.starAlgEquiv_mem_iff_of_symm_map_eq
#print axioms ThomGame.Analysis.unitaryRepresentationCommutant_normalizer_of_pullback_eq
#print axioms ThomGame.Analysis.matrixThom_groupCentralizer_normalized
#print axioms ThomGame.Analysis.unitaryRepresentationCommutant_eq_generatorCommutant
#print axioms ThomGame.Analysis.exists_matrixRepresentation_internal_commutant_of_gap
#print axioms ThomGame.Analysis.matrixThom_groupCentralizer_normalized_of_spectral_gaps
#print axioms ThomGame.Construction.compressor_matrixCentralizer_normalized
#print axioms ThomGame.Construction.lambda_matrix_J_eq_one_of_internal_commutants
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial_of_compressor_internality
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_compressor_internality
#print axioms ThomGame.Compressor.generatorTuple_range
#print axioms ThomGame.Compressor.positiveGeneratorTuple_range
#print axioms ThomGame.Compressor.generatorTuple_generates
#print axioms ThomGame.Compressor.positiveGeneratorTuple_generates
#print axioms ThomGame.Construction.compressor_internality_of_spectral_gaps
#print axioms ThomGame.Construction.lambda_matrix_J_eq_one_of_compressor_spectral_gaps
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial_of_compressor_spectral_gaps
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_compressor_spectral_gaps

-- Explicit prime-five rank-three covers, their actual N/H images, and the shear quotient.
#print axioms ThomGame.PrimeFiveRankThreeCover.relators_finite
#print axioms ThomGame.PrimeFiveRankThreeCover.generator_card
#print axioms ThomGame.PrimeFiveRankThreeCover.intermediate_unique
#print axioms ThomGame.PrimeFiveRankThreeCover.third_eq_of_ne
#print axioms ThomGame.PrimeFiveRankThreeCover.path_indices
#print axioms ThomGame.PrimeFiveRankThreeCover.e5_tautology
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.eval_relator
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.toHom_of
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.range_toHom
#print axioms ThomGame.PrimeFiveRankThreeCover.of_e0
#print axioms ThomGame.PrimeFiveRankThreeCover.of_e1
#print axioms ThomGame.PrimeFiveRankThreeCover.of_e2
#print axioms ThomGame.PrimeFiveRankThreeCover.of_e3
#print axioms ThomGame.PrimeFiveRankThreeCover.of_e4
#print axioms ThomGame.Compressor.elementary_e0
#print axioms ThomGame.Compressor.elementary_e1
#print axioms ThomGame.Compressor.elementary_e2
#print axioms ThomGame.Compressor.elementary_e3
#print axioms ThomGame.Compressor.elementary_e4
#print axioms ThomGame.Compressor.coverToQ_of
#print axioms ThomGame.Compressor.coverToQ_range
#print axioms ThomGame.Compressor.fullCoverCoefficient_none
#print axioms ThomGame.Compressor.positiveCoverCoefficient_none
#print axioms ThomGame.Compressor.fullCoverCoefficient_surjective
#print axioms ThomGame.Compressor.fullCoverToQ_range
#print axioms ThomGame.Compressor.positiveCoverToQ_range
#print axioms ThomGame.Compressor.coverToElementary_surjective
#print axioms ThomGame.Compressor.coverToPositive_surjective
#print axioms ThomGame.Compressor.coverToElementary_of
#print axioms ThomGame.Compressor.coverToPositive_of
#print axioms ThomGame.IntegralShear.relation_card
#print axioms ThomGame.IntegralShear.relators_finite
#print axioms ThomGame.IntegralShear.Model.eval_relator
#print axioms ThomGame.IntegralShear.Model.toHom_of
#print axioms ThomGame.Compressor.shear_comm_relation
#print axioms ThomGame.Compressor.shear_root_relation
#print axioms ThomGame.Compressor.shear_torsion_relation
#print axioms ThomGame.Compressor.integralShearToQ_of
#print axioms ThomGame.Compressor.integralShearToQuotient_of
#print axioms ThomGame.Compressor.elementaryQuotient_elementary
#print axioms ThomGame.Compressor.integralShearToQuotient_surjective

-- Actual finite root/pair structure and Hilbert invariant averages.
#print axioms ThomGame.commutingClosure_pow
#print axioms ThomGame.commutingClosure_finite
#print axioms ThomGame.finite_of_commuting_generators
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.x_mem_rootSubgroup
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.root_generators_commute
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.root_range_commute
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.rootSubgroup_pow
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.rootSubgroup_finite
#print axioms ThomGame.PrimeFiveRankThreeCover.of_mem_rootSubgroup
#print axioms ThomGame.PrimeFiveRankThreeCover.rootSubgroup_pow
#print axioms ThomGame.PrimeFiveRankThreeCover.rootSubgroup_finite
#print axioms ThomGame.PrimeFiveRankThreeCover.right_cyclicRoot
#print axioms ThomGame.PrimeFiveRankThreeCover.cyclic_or_across
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.x_mem_cyclicSup
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.range_eq_cyclicSup
#print axioms ThomGame.PrimeFiveRankThreeCover.cyclicRootSubgroups_generate
#print axioms ThomGame.quotient_generators_generate
#print axioms ThomGame.quotient_commutes_of_generator_commutators
#print axioms ThomGame.generatorCommutatorSubgroup_le_center
#print axioms ThomGame.commutator_eq_generatorCommutatorSubgroup
#print axioms ThomGame.commutator_le_center_of_generators
#print axioms ThomGame.generatorCommutatorSubgroup_finite
#print axioms ThomGame.finite_of_central_commutator_generators
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairGenerator_range
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_eq_sup
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairOf_generates
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.cross_commutes_left
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.cross_commutes_right
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairGenerator_triple
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairOf_triple
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairOf_pow
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_commutator_le_center
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_finite
#print axioms ThomGame.generatorCommutatorSubgroup_pow
#print axioms ThomGame.pow_square_of_central_commutator_generators
#print axioms ThomGame.isPGroup_of_central_commutator_generators
#print axioms ThomGame.upperCentralSeries_two_of_commutator_le_center
#print axioms ThomGame.nilpotent_of_commutator_le_center
#print axioms ThomGame.nilpotencyClass_le_two_of_commutator_le_center
#print axioms ThomGame.prime_le_index_of_proper
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.rootSubgroup_isPGroup
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_isPGroup
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_nilpotent
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_nilpotencyClass_le_two
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_card
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.rootSubgroup_proper_index
#print axioms ThomGame.PrimeFiveRankThreeCover.Model.pairSubgroup_proper_index
#print axioms ThomGame.PrimeFiveRankThreeCover.cyclic_pairSubgroup
#print axioms ThomGame.PrimeFiveRankThreeCover.pairSubgroup_finite
#print axioms ThomGame.PrimeFiveRankThreeCover.pairSubgroup_isPGroup
#print axioms ThomGame.PrimeFiveRankThreeCover.pairSubgroup_nilpotencyClass_le_two
#print axioms ThomGame.Analysis.mem_hilbertUnitaryInvariants
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_isClosed
#print axioms ThomGame.Analysis.hilbertUnitary_apply_mul
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_of_iSup
#print axioms ThomGame.Analysis.hilbertUnitary_inner_fixed_left
#print axioms ThomGame.Analysis.hilbertUnitary_fixed_of_generators
#print axioms ThomGame.Analysis.finiteUnitaryAverage_apply
#print axioms ThomGame.Analysis.finiteUnitaryAverage_invariant
#print axioms ThomGame.Analysis.finiteUnitaryAverage_of_invariant
#print axioms ThomGame.Analysis.finiteUnitaryAverage_inner_fixed
#print axioms ThomGame.Analysis.finiteUnitaryAverage_residual_orthogonal
#print axioms ThomGame.Analysis.finiteUnitaryAverage_eq_projection
#print axioms ThomGame.Analysis.finiteUnitaryAverage_isStarProjection
#print axioms ThomGame.Analysis.finiteUnitaryAverage_norm_le
#print axioms ThomGame.Analysis.finiteUnitaryAverage_eq_self_iff
#print axioms ThomGame.Analysis.finiteUnitary_sum_eq_card_average
#print axioms ThomGame.Analysis.finiteUnitaryAverage_residual_zero
#print axioms ThomGame.Analysis.finiteUnitary_displacement_residual
#print axioms ThomGame.Analysis.finiteUnitary_energy_identity
#print axioms ThomGame.Analysis.finiteUnitary_residual_sq_le
#print axioms ThomGame.Analysis.finiteSubgroupAverage_invariant
#print axioms ThomGame.Analysis.finiteSubgroupAverage_of_invariant
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_subgroup_mono
#print axioms ThomGame.Analysis.finiteSubgroupAverage_mul_of_le
#print axioms ThomGame.Analysis.finiteSubgroupAverage_energy
#print axioms ThomGame.Analysis.finiteSubgroupAverage_eq_projection
#print axioms ThomGame.Analysis.finiteSubgroupAverage_isStarProjection
#print axioms ThomGame.Analysis.finiteSubgroupAverage_norm_le
#print axioms ThomGame.Analysis.finiteSubgroupAverage_mul_of_ge
#print axioms ThomGame.Analysis.cover_invariants_eq_cyclic_invariants
#print axioms ThomGame.Analysis.coverRootAverage_mul_pairAverage
#print axioms ThomGame.Analysis.coverNextRootAverage_mul_pairAverage
#print axioms ThomGame.Analysis.coverRootAverage_isStarProjection
#print axioms ThomGame.Analysis.coverPairAverage_isStarProjection
#print axioms ThomGame.Analysis.coverPairAverage_mul_rootAverage
#print axioms ThomGame.Analysis.coverPairAverage_mul_nextRootAverage

-- Finite central Fourier decomposition and the actual cover root-pair angle bound.
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_apply
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_inv
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_norm
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_ne_zero
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_conj
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_trivial
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_sum
#print axioms ThomGame.Analysis.finiteGroupCharacterHom_injective
#print axioms ThomGame.Analysis.finiteCharacterAverage_apply
#print axioms ThomGame.Analysis.finiteCharacterAverage_trivial
#print axioms ThomGame.Analysis.finiteCharacterAverage_eigen
#print axioms ThomGame.Analysis.finiteCharacterAverage_of_eigen
#print axioms ThomGame.Analysis.finiteCharacterAverage_sum
#print axioms ThomGame.Analysis.finiteCharacterAverage_commute
#print axioms ThomGame.Analysis.finiteCharacterSpace_isClosed
#print axioms ThomGame.Analysis.finiteCharacter_inner_eigen_left
#print axioms ThomGame.Analysis.finiteCharacterSpace_orthogonal
#print axioms ThomGame.Analysis.finiteCharacterAverage_inner_eigen
#print axioms ThomGame.Analysis.finiteCharacterAverage_residual_orthogonal
#print axioms ThomGame.Analysis.finiteCharacterAverage_orthogonal
#print axioms ThomGame.Analysis.finiteCharacterAverage_eq_projection
#print axioms ThomGame.Analysis.finiteCharacterAverage_isStarProjection
#print axioms ThomGame.Analysis.finiteCharacterSpace_orthogonalFamily
#print axioms ThomGame.Analysis.finiteCharacterSpace_norm_sum
#print axioms ThomGame.Analysis.finiteCharacterAverage_norm_decomposition
#print axioms ThomGame.Analysis.finiteCharacterSpace_map_mem
#print axioms ThomGame.Analysis.finiteCharacterDecomposition_bound
#print axioms ThomGame.centralCommutator_mul_right
#print axioms ThomGame.mem_commutatorCharacterAnnihilator
#print axioms ThomGame.commutatorCharacterAnnihilator_index
#print axioms ThomGame.commutator_character_eq_one_of_cross
#print axioms ThomGame.commutatorCharacterAnnihilator_ne_top
#print axioms ThomGame.Analysis.finiteUnitaryAverage_apply_unitary
#print axioms ThomGame.Analysis.finiteUnitaryAverage_commute
#print axioms ThomGame.Analysis.finiteSubgroupAverage_apply_unitary
#print axioms ThomGame.Analysis.finiteSubgroupAverage_commute
#print axioms ThomGame.Analysis.finiteSubgroupAverage_eq_zero_of_eigen
#print axioms ThomGame.Analysis.finiteSubgroupAverage_inner_fixed
#print axioms ThomGame.Analysis.finiteSubgroupAverage_norm_sq
#print axioms ThomGame.Analysis.centralCharacter_translate_eigen
#print axioms ThomGame.Analysis.finiteAverage_translate_vanishes
#print axioms ThomGame.Analysis.finiteAverage_translate_fixed
#print axioms ThomGame.Analysis.finiteAverage_support_bound
#print axioms ThomGame.Analysis.centralCharacter_sandwich_bound
#print axioms ThomGame.Analysis.centralCharacter_average_norm_sq
#print axioms ThomGame.Analysis.centralCharacter_prime_angle_sq
#print axioms ThomGame.Analysis.finiteSubgroupAverage_central_commute
#print axioms ThomGame.Analysis.finiteSubgroupAverage_preserves_central_character
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_of_sup
#print axioms ThomGame.Analysis.finiteAverage_trivial_character_invariant
#print axioms ThomGame.Analysis.eq_zero_of_character_and_global_invariant
#print axioms ThomGame.Analysis.finiteAverage_global_eq_zero_of_nontrivial_character
#print axioms ThomGame.Analysis.finiteAverage_trivial_character_product
#print axioms ThomGame.Analysis.finiteSubgroupAverage_apply_norm_le
#print axioms ThomGame.Analysis.finiteClassTwo_pair_angle_sq
#print axioms ThomGame.Analysis.finiteClassTwo_pair_angle
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_subgroupOf
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_top
#print axioms ThomGame.Analysis.finiteSubgroupAverage_subgroupOf
#print axioms ThomGame.Analysis.finiteSubgroupAverage_restrict_top
#print axioms ThomGame.Analysis.subgroupOf_commutes
#print axioms ThomGame.Analysis.coverRootAverage_pair_angle
#print axioms ThomGame.Analysis.coverRootAverage_reverse_pair_angle
#print axioms ThomGame.Analysis.primeFive_angle_lt_half
#print axioms ThomGame.Analysis.coverRootAverage_pair_angle_lt_half

#print axioms ThomGame.Analysis.starProjection_apply_apply
#print axioms ThomGame.Analysis.starProjection_inner_symm
#print axioms ThomGame.Analysis.starProjection_norm_sq
#print axioms ThomGame.Analysis.starProjection_cross_inner_le
#print axioms ThomGame.Analysis.starProjection_add_norm_le
#print axioms ThomGame.Analysis.positive_polynomial_gap_on_range
#print axioms ThomGame.Analysis.positive_polynomial_gap
#print axioms ThomGame.Analysis.starProjection_pair_residual_lower
#print axioms ThomGame.Analysis.starProjection_pair_residual_polynomial
#print axioms ThomGame.Analysis.projectionLaplacian_nonneg
#print axioms ThomGame.Analysis.projectionLaplacian_energy
#print axioms ThomGame.Analysis.projectionLaplacian_mem_ker_iff
#print axioms ThomGame.Analysis.projectionLaplacian_ker
#print axioms ThomGame.Analysis.threeStarProjections_polynomial
#print axioms ThomGame.Analysis.threeProjectionLaplacian_polynomial
#print axioms ThomGame.Analysis.threeProjectionLaplacian_gap
#print axioms ThomGame.Analysis.primeFiveRootGap_pos
#print axioms ThomGame.Analysis.coverRootAverage_eqLocus
#print axioms ThomGame.Analysis.coverRootLaplacian_nonneg
#print axioms ThomGame.Analysis.coverRootLaplacian_ker
#print axioms ThomGame.Analysis.coverRootLaplacian_energy
#print axioms ThomGame.Analysis.coverRootLaplacian_polynomial
#print axioms ThomGame.Analysis.coverRootLaplacian_gap
#print axioms ThomGame.Analysis.coverRootAverage_residual_sq_le
#print axioms ThomGame.Analysis.coverRootLaplacian_displacement_gap
#print axioms ThomGame.PrimeFiveRankThreeCover.mem_rootGeneratingSet
#print axioms ThomGame.PrimeFiveRankThreeCover.one_mem_rootGeneratingSet
#print axioms ThomGame.PrimeFiveRankThreeCover.rootGeneratingSet_nonempty
#print axioms ThomGame.PrimeFiveRankThreeCover.rootGeneratingSet_generates
#print axioms ThomGame.Analysis.primeFiveKazhdanConstant_pos
#print axioms ThomGame.Analysis.primeFiveKazhdanConstant_sq
#print axioms ThomGame.Analysis.coverRootGeneratingSet_displacement
#print axioms ThomGame.Analysis.coverRootGeneratingSet_nonzero_invariant
#print axioms ThomGame.Analysis.finiteGeneratingSet_image_generates
#print axioms ThomGame.Analysis.coverQuotientGeneratingSet_generates
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_comp_surjective
#print axioms ThomGame.Analysis.coverQuotientGeneratingSet_displacement
#print axioms ThomGame.Analysis.coverQuotientGeneratingSet_nonzero_invariant
#print axioms ThomGame.Compressor.elementaryKazhdanSet_generates
#print axioms ThomGame.Compressor.positiveKazhdanSet_generates
#print axioms ThomGame.Compressor.elementaryKazhdanSet_displacement
#print axioms ThomGame.Compressor.positiveKazhdanSet_displacement
#print axioms ThomGame.Compressor.elementaryKazhdanSet_nonzero_invariant
#print axioms ThomGame.Compressor.positiveKazhdanSet_nonzero_invariant
#print axioms ThomGame.exists_generatorWordBound
#print axioms ThomGame.finiteSet_generatorWordBounds
#print axioms ThomGame.finiteSetWordConstant_pos
#print axioms ThomGame.finiteSetWordConstant_spec
#print axioms ThomGame.Analysis.hilbertUnitary_mul_displacement_le
#print axioms ThomGame.Analysis.hilbertUnitary_inv_displacement
#print axioms ThomGame.Analysis.generatorWordBound_displacement
#print axioms ThomGame.Analysis.finiteSetWordConstant_displacement
#print axioms ThomGame.Compressor.positiveKazhdanSetInQ_mem_closure
#print axioms ThomGame.Compressor.positiveGeneratorWordConstant_pos
#print axioms ThomGame.Compressor.positiveGeneratorKazhdanConstant_pos
#print axioms ThomGame.Compressor.positiveGeneratorTuple_displacement
#print axioms ThomGame.Compressor.positiveGeneratorTuple_energy_gap

#print axioms ThomGame.Analysis.matrixHilbertConjugationOperator_embedding
#print axioms ThomGame.Analysis.matrixUltratrace_conjugation
#print axioms ThomGame.Analysis.matrixHilbertConjugationOperator_one
#print axioms ThomGame.Analysis.matrixHilbertConjugationOperator_mul
#print axioms ThomGame.Analysis.matrixHilbertConjugationOperator_norm
#print axioms ThomGame.Analysis.matrixHilbertConjugation_embedding
#print axioms ThomGame.Analysis.matrixHilbertConjugationHom_embedding
#print axioms ThomGame.Analysis.matrixHilbertConjugationHom_symm_embedding
#print axioms ThomGame.Analysis.matrixUniformLazyMarkov_sequence_formula
#print axioms ThomGame.Analysis.matrixQuotientLazyMarkov_formula
#print axioms ThomGame.Analysis.matrixLazyMarkov_hilbertMap_eq_average
#print axioms ThomGame.Analysis.matrixLazyMarkov_hilbert_conjugation_energy
#print axioms ThomGame.Analysis.representationMarkovGapConstant_pos
#print axioms ThomGame.Analysis.representationMarkovGapConstant_lt_one
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_generated_iff
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_eq_average_fixed
#print axioms ThomGame.Analysis.matrixConjugationRepresentation_embedding
#print axioms ThomGame.Analysis.matrixRepresentation_hilbertMap_eq_average
#print axioms ThomGame.Analysis.matrixRepresentation_hilbert_energy
#print axioms ThomGame.Analysis.matrixRepresentation_relativeTrace_eq_invariants
#print axioms ThomGame.Analysis.matrixMarkovSpectralGap_of_representation_energy
#print axioms ThomGame.Analysis.exists_matrixTuple_unitary_lift
#print axioms ThomGame.Compressor.positiveMarkovGapConstant_pos
#print axioms ThomGame.Compressor.positiveMarkovGapConstant_lt_one
#print axioms ThomGame.Compressor.positiveMarkovGapConstant_formula
#print axioms ThomGame.Compressor.positiveGeneratorTuple_matrixGap
#print axioms ThomGame.Compressor.exists_positiveGeneratorTuple_matrixGap
#print axioms ThomGame.Construction.compressor_positive_commutant_internal
#print axioms ThomGame.Construction.compressor_spectral_gaps_iff_Q_gap
#print axioms ThomGame.Construction.compressor_internality_of_Q_spectral_gap
#print axioms ThomGame.Construction.lambda_matrix_J_eq_one_of_Q_spectral_gap
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial_of_Q_spectral_gaps
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_Q_spectral_gaps

#print axioms ThomGame.Analysis.hilbertUnitaryRestriction_apply
#print axioms ThomGame.Analysis.normalInvariants_stable
#print axioms ThomGame.Analysis.normalInvariantsRepresentation_apply
#print axioms ThomGame.Analysis.normalInvariantsRepresentation_kernel
#print axioms ThomGame.Analysis.normalQuotientRepresentation_mk
#print axioms ThomGame.Analysis.normalQuotientRepresentation_invariant_iff
#print axioms ThomGame.Analysis.hilbertUnitary_submodule_map
#print axioms ThomGame.Analysis.hilbertUnitary_projection_commute
#print axioms ThomGame.Analysis.normalInvariantVector_displacement_le
#print axioms ThomGame.Analysis.normalInvariantVector_orthogonal
#print axioms ThomGame.Analysis.normalInvariantResidual_orthogonal
#print axioms ThomGame.Analysis.normalInvariantResidual_displacement
#print axioms ThomGame.Analysis.hilbertKazhdanBound_image
#print axioms ThomGame.Analysis.hasFiniteHilbertKazhdanSet_surjective
#print axioms ThomGame.Analysis.hilbertKazhdanBound_nonzero_invariant
#print axioms ThomGame.Analysis.normalExtensionKazhdanConstant_pos
#print axioms ThomGame.Analysis.hilbertKazhdanBound_normalExtension
#print axioms ThomGame.Analysis.hasFiniteHilbertKazhdanSet_normalExtension
#print axioms ThomGame.Analysis.generatingTuple_mem_closure
#print axioms ThomGame.Analysis.generatingTupleWordConstant_pos
#print axioms ThomGame.Analysis.generatingTupleKazhdanConstant_pos
#print axioms ThomGame.Analysis.generatingTuple_displacement_of_kazhdanBound
#print axioms ThomGame.Analysis.generatingTuple_energy_of_kazhdanBound
#print axioms ThomGame.Analysis.exists_generatingTuple_energy_gap
#print axioms ThomGame.Compressor.elementaryHilbertKazhdanBound
#print axioms ThomGame.Compressor.shearExtensionKazhdanConstant_pos
#print axioms ThomGame.Compressor.hilbertKazhdanBound_of_shear
#print axioms ThomGame.Compressor.hasFiniteHilbertKazhdanSet_of_shear
#print axioms ThomGame.Compressor.shearGeneratorWordConstant_pos
#print axioms ThomGame.Compressor.shearGeneratorKazhdanConstant_formula
#print axioms ThomGame.Compressor.shearGeneratorKazhdanConstant_pos
#print axioms ThomGame.Compressor.generatorTuple_displacement_of_shear
#print axioms ThomGame.Compressor.generatorTuple_energy_of_shear
#print axioms ThomGame.Compressor.exists_generatorTuple_energy_gap_of_shear
#print axioms ThomGame.Compressor.shearMarkovGapConstant_pos
#print axioms ThomGame.Compressor.shearMarkovGapConstant_lt_one
#print axioms ThomGame.Compressor.shearMarkovGapConstant_formula
#print axioms ThomGame.Compressor.generatorTuple_matrixGap_of_shear
#print axioms ThomGame.Compressor.exists_generatorTuple_matrixGap_of_shear
#print axioms ThomGame.Compressor.exists_uniform_generatorTuple_matrixGap_of_shear
#print axioms ThomGame.Construction.compressor_Q_spectral_gap_of_shear
#print axioms ThomGame.Construction.compressor_spectral_gaps_of_shear
#print axioms ThomGame.Construction.compressor_internality_of_shear
#print axioms ThomGame.Construction.lambda_matrix_J_eq_one_of_shear
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial_of_shear
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_shear

#print axioms ThomGame.centralCommutator_inv_left
#print axioms ThomGame.centralCommutator_zpow_left
#print axioms ThomGame.centralCommutator_zpow_right
#print axioms ThomGame.centralCommutator_zpow_zpow
#print axioms ThomGame.IntegralShear.of_commute
#print axioms ThomGame.IntegralShear.of_commutator
#print axioms ThomGame.IntegralShear.of_torsion
#print axioms ThomGame.IntegralShear.rootElement_zero
#print axioms ThomGame.IntegralShear.rootElement_one
#print axioms ThomGame.IntegralShear.rootElement_add
#print axioms ThomGame.IntegralShear.rootElement_neg
#print axioms ThomGame.IntegralShear.rootElement_commute
#print axioms ThomGame.IntegralShear.rootElement_commutator
#print axioms ThomGame.IntegralShear.rootElement_conjugate
#print axioms ThomGame.IntegralShear.rootElements_generate
#print axioms ThomGame.IntegralShear.toIntegralMatrix_of
#print axioms ThomGame.IntegralShear.integral_elem_zpow
#print axioms ThomGame.IntegralShear.toIntegralMatrix_rootElement
#print axioms ThomGame.IntegralShear.toIntegralMatrix_rootElement_entry
#print axioms ThomGame.IntegralShear.rootElement_injective
#print axioms ThomGame.IntegralShear.rootElement_eq_one_iff
#print axioms ThomGame.IntegralShear.rootPlane_factors_commute
#print axioms ThomGame.IntegralShear.rootPlaneElement_zero
#print axioms ThomGame.IntegralShear.rootPlaneElement_add
#print axioms ThomGame.IntegralShear.toIntegralMatrix_rootPlaneElement
#print axioms ThomGame.IntegralShear.rootPlaneElement_injective
#print axioms ThomGame.IntegralShear.rootPlaneHom_injective
#print axioms ThomGame.IntegralShear.rootPlaneElement_conjugate_upper
#print axioms ThomGame.IntegralShear.rootPlaneElement_conjugate_lower
#print axioms ThomGame.IntegerPlane.freeAction_of
#print axioms ThomGame.IntegerPlane.upperShear_apply
#print axioms ThomGame.IntegerPlane.lowerShear_apply
#print axioms ThomGame.IntegralShear.freeRootPair_of
#print axioms ThomGame.IntegralShear.rootPlaneHom_equivariant
#print axioms ThomGame.IntegralShear.rootPlaneSemidirectHom_inl
#print axioms ThomGame.IntegralShear.rootPlaneSemidirectHom_inr
#print axioms ThomGame.IntegralShear.rootPlaneSemidirectHom_inl_injective
#print axioms ThomGame.IntegerSteinberg.Model.eval_relator
#print axioms ThomGame.IntegerSteinberg.Model.toHom_of
#print axioms ThomGame.IntegerSteinberg.Model.x_zero
#print axioms ThomGame.IntegerSteinberg.Model.x_eq_zpow
#print axioms ThomGame.IntegerSteinberg.Model.adjacent_indices
#print axioms ThomGame.IntegerSteinberg.of_additive
#print axioms ThomGame.IntegerSteinberg.of_commute
#print axioms ThomGame.IntegerSteinberg.of_adjacent
#print axioms ThomGame.IntegerSteinberg.of_eq_zpow
#print axioms ThomGame.IntegerSteinberg.unitRootElements_generate
#print axioms ThomGame.IntegerSteinberg.toShear_of
#print axioms ThomGame.IntegerSteinberg.toShear_surjective
#print axioms ThomGame.Construction.shear_hasFiniteHilbertKazhdanSet_of_integerSteinberg
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial_of_integerSteinberg

#print axioms ThomGame.Analysis.IntegerTorus.rep_mem
#print axioms ThomGame.Analysis.IntegerTorus.rep_abs_le
#print axioms ThomGame.Analysis.IntegerTorus.rep_measurable
#print axioms ThomGame.Analysis.IntegerTorus.coe_rep
#print axioms ThomGame.Analysis.IntegerTorus.rep_coe
#print axioms ThomGame.Analysis.IntegerTorus.rep_zero
#print axioms ThomGame.Analysis.IntegerTorus.rep_eq_zero_iff
#print axioms ThomGame.Analysis.IntegerTorus.ofReal_pointRep
#print axioms ThomGame.Analysis.IntegerTorus.pointRep_ofReal
#print axioms ThomGame.Analysis.IntegerTorus.pointRep_eq_zero_iff
#print axioms ThomGame.Analysis.IntegerTorus.lower_ofReal
#print axioms ThomGame.Analysis.IntegerTorus.upper_ofReal
#print axioms ThomGame.Analysis.IntegerTorus.smallSquare_measurable
#print axioms ThomGame.Analysis.IntegerTorus.cone_measurable
#print axioms ThomGame.Analysis.IntegerTorus.cones_disjoint
#print axioms ThomGame.Analysis.IntegerTorus.cones_union
#print axioms ThomGame.Analysis.IntegerTorus.shear_abs_bounds
#print axioms ThomGame.Analysis.IntegerTorus.shear_small
#print axioms ThomGame.Analysis.IntegerTorus.lower_rep_on_small
#print axioms ThomGame.Analysis.IntegerTorus.upper_rep_on_small
#print axioms ThomGame.Analysis.IntegerTorus.coneImage_subset_band
#print axioms ThomGame.Analysis.IntegerTorus.bands_pairwise_disjoint
#print axioms ThomGame.Analysis.IntegerTorus.coneImages_pairwise_disjoint
#print axioms ThomGame.Analysis.IntegerTorus.coneImage_measurable
#print axioms ThomGame.Analysis.IntegerTorus.coneImage_mass_sum_le
#print axioms ThomGame.Analysis.IntegerTorus.cone_masses_of_origin_null
#print axioms ThomGame.Analysis.IntegerTorus.packing_bound
#print axioms ThomGame.Analysis.IntegerTorus.outside_mass_lower_bound
#print axioms ThomGame.Analysis.IntegerTorus.character_continuous
#print axioms ThomGame.Analysis.IntegerTorus.character_zero
#print axioms ThomGame.Analysis.IntegerTorus.character_add
#print axioms ThomGame.Analysis.IntegerTorus.character_norm
#print axioms ThomGame.Analysis.IntegerTorus.character_rep
#print axioms ThomGame.Analysis.IntegerTorus.character_chord_lower
#print axioms ThomGame.Analysis.IntegerTorus.character_chord_upper
#print axioms ThomGame.Analysis.IntegerTorus.coordinateEnergy_nonneg
#print axioms ThomGame.Analysis.IntegerTorus.coordinateEnergy_continuous
#print axioms ThomGame.Analysis.IntegerTorus.coordinateEnergy_le_eight
#print axioms ThomGame.Analysis.IntegerTorus.coordinateEnergy_integrable
#print axioms ThomGame.Analysis.IntegerTorus.coordinateEnergy_lower_outside
#print axioms ThomGame.Analysis.IntegerTorus.outside_mass_le_energy
#print axioms ThomGame.Analysis.IntegerTorus.integerShear_zero
#print axioms ThomGame.Analysis.IntegerTorus.integerShear_add
#print axioms ThomGame.Analysis.IntegerTorus.integerShear_nat_succ_image
#print axioms ThomGame.Analysis.IntegerTorus.integerShear_measure_error
#print axioms ThomGame.Analysis.IntegerTorus.cone_measure_errors_of_unit_shears
#print axioms ThomGame.Analysis.IntegerTorus.measure_energy_defect_bound
#print axioms ThomGame.Analysis.IntegerTorus.measure_quadratic_defect_bound
#print axioms ThomGame.Analysis.IntegerTorus.no_almost_invariant_measure
#print axioms ThomGame.Analysis.hilbertVectorState_sub_identity
#print axioms ThomGame.Analysis.hilbertVectorState_sub_norm_le
#print axioms ThomGame.Analysis.hilbertVectorState_re_sub_abs_le
#print axioms ThomGame.Analysis.hilbertVectorState_unit_contraction_bound
#print axioms ThomGame.Analysis.hilbertVectorState_unit_contraction_re_bound
#print axioms ThomGame.Analysis.IntegerTorus.character_eq_one_iff
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_continuous
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_norm
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_zero
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_add
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_first
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_second
#print axioms ThomGame.Analysis.IntegerTorus.coordinate_characters_eq_one_iff
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_upperShear
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_lowerShear
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_shear
#print axioms ThomGame.Analysis.IntegerTorus.latticeCharacter_freeAction_generator

#print axioms ThomGame.Analysis.IntegerTorus.character_spectralCoordinate
#print axioms ThomGame.Analysis.IntegerTorus.gelfand_torusFunctionalCalculus
#print axioms ThomGame.Analysis.IntegerTorus.torusFunctionalCalculus_first
#print axioms ThomGame.Analysis.IntegerTorus.torusFunctionalCalculus_second
#print axioms ThomGame.Analysis.IntegerTorus.torusFunctionalCalculus_norm_le
#print axioms ThomGame.Analysis.CommutingUnitaryPair.first_mem_algebra
#print axioms ThomGame.Analysis.CommutingUnitaryPair.second_mem_algebra
#print axioms ThomGame.Analysis.CommutingUnitaryPair.calculus_first
#print axioms ThomGame.Analysis.CommutingUnitaryPair.calculus_second
#print axioms ThomGame.Analysis.CommutingUnitaryPair.calculus_norm_le
#print axioms ThomGame.Analysis.CommutingUnitaryPair.ofIsometries_calculus_first
#print axioms ThomGame.Analysis.CommutingUnitaryPair.ofIsometries_calculus_second
#print axioms ThomGame.Analysis.continuousComplexify_apply
#print axioms ThomGame.Analysis.continuousComplexify_add
#print axioms ThomGame.Analysis.continuousComplexify_smul
#print axioms ThomGame.Analysis.continuousComplexify_one
#print axioms ThomGame.Analysis.hilbertContinuousVectorState_apply
#print axioms ThomGame.Analysis.continuousComplexify_nonneg_factor
#print axioms ThomGame.Analysis.hilbertContinuousVectorState_nonneg
#print axioms ThomGame.Analysis.hilbertContinuousVectorState_one
#print axioms ThomGame.Analysis.hilbertCompactVectorState_apply
#print axioms ThomGame.Analysis.hilbertVectorMeasure_integral
#print axioms ThomGame.Analysis.hilbertVectorMeasure_mass
#print axioms ThomGame.Analysis.hilbertVectorMeasure_probability
#print axioms ThomGame.Analysis.continuousComplexify_normSq
#print axioms ThomGame.Analysis.hilbertVectorMeasure_integral_normSq
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_mass
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_probability
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_first_energy
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_second_energy
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_energy
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_energy_le
#print axioms ThomGame.Analysis.CommutingUnitaryPair.ofIsometries_spectralMeasure_energy
#print axioms ThomGame.Analysis.continuousCesaro_at_one
#print axioms ThomGame.Analysis.hilbertCalculus_pow_apply
#print axioms ThomGame.Analysis.hilbertCalculus_cesaro_apply
#print axioms ThomGame.Analysis.hilbertVectorMeasure_atom_le_normSq
#print axioms ThomGame.Analysis.hilbertVectorMeasure_atom_zero_of_orthogonal
#print axioms ThomGame.Analysis.torusOriginCutoff_zero
#print axioms ThomGame.Analysis.torusOriginCutoff_norm_le
#print axioms ThomGame.Analysis.CommutingUnitaryPair.torusOriginCutoff_calculus_norm_le
#print axioms ThomGame.Analysis.CommutingUnitaryPair.torusOriginCutoff_fixed_common
#print axioms ThomGame.Analysis.CommutingUnitaryPair.spectralMeasure_origin_null
#print axioms ThomGame.Analysis.measureReal_compact_le_of_continuous_integral_le
#print axioms ThomGame.Analysis.measureReal_borel_le_of_continuous_integral_le
#print axioms ThomGame.Analysis.continuousComplexify_norm_le_one
#print axioms ThomGame.Analysis.hilbertVectorMeasure_borel_le
#print axioms ThomGame.Analysis.hilbertVectorMeasure_borel_sub_abs_le
#print axioms ThomGame.Analysis.hilbertVectorMeasure_unit_borel_sub_abs_le
#print axioms ThomGame.Analysis.lattice_generator_decomposition
#print axioms ThomGame.Analysis.latticeUnitaryPair_commonFixed
#print axioms ThomGame.Analysis.latticeSpectralMeasure_probability
#print axioms ThomGame.Analysis.latticeSpectralMeasure_origin_null
#print axioms ThomGame.Analysis.latticeSpectralMeasure_energy
#print axioms ThomGame.Analysis.latticeSpectralMeasure_energy_le
#print axioms ThomGame.Analysis.latticeSpectralMeasure_borel_perturbation

#print axioms ThomGame.Analysis.IntegerTorus.character_injective
#print axioms ThomGame.Analysis.IntegerTorus.coordinateCharacter_mem
#print axioms ThomGame.Analysis.IntegerTorus.coordinateAlgebra_separatesPoints
#print axioms ThomGame.Analysis.IntegerTorus.coordinateAlgebra_dense
#print axioms ThomGame.Analysis.IntegerTorus.torusStarAlgHom_ext
#print axioms ThomGame.Analysis.hilbertVectorMeasure_map_of_covariant
#print axioms ThomGame.Analysis.hilbertVectorMeasure_image_of_covariant
#print axioms ThomGame.Analysis.hilbertVectorMeasure_shear_bound_of_covariant
#print axioms ThomGame.Analysis.coordinateCharacter_shear
#print axioms ThomGame.Analysis.lattice_shear_generator
#print axioms ThomGame.Analysis.latticeCalculus_coordinate
#print axioms ThomGame.Analysis.latticeCalculus_sheared_coordinate
#print axioms ThomGame.Analysis.latticeCalculus_shear_covariant
#print axioms ThomGame.Analysis.latticeSpectralMeasure_shear_map
#print axioms ThomGame.Analysis.latticeSpectralMeasure_shear_image
#print axioms ThomGame.Analysis.latticeSpectralMeasure_shear_bound
#print axioms ThomGame.Analysis.latticeShear_no_small_unit_vector
#print axioms ThomGame.Analysis.hilbertRelativeKazhdanBound_image
#print axioms ThomGame.Analysis.hilbertRelativeKazhdanBound_nonzero_invariant
#print axioms ThomGame.Analysis.freeShear_representation_conjugate
#print axioms ThomGame.Analysis.freeShear_no_small_unit_vector
#print axioms ThomGame.Analysis.freeShear_unit_displacement
#print axioms ThomGame.Analysis.freeShear_relative_displacement
#print axioms ThomGame.Analysis.freeShear_relativeKazhdanBound
#print axioms ThomGame.Analysis.rootPlaneHom_latticeGenerator
#print axioms ThomGame.Analysis.rootPlaneSemidirectHom_generator
#print axioms ThomGame.Analysis.rootPlaneSemidirectHom_comp_inl
#print axioms ThomGame.Analysis.rootPlaneKazhdanSet_image
#print axioms ThomGame.Analysis.rootPlane_relativeKazhdanBound
#print axioms ThomGame.Analysis.rootPlane_nonzero_invariant
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_comp_range
#print axioms ThomGame.Analysis.hilbertUnitaryInvariants_comp_stable
#print axioms ThomGame.Analysis.hilbertRelativeInvariantResidual_displacement_le
#print axioms ThomGame.Analysis.hilbertRelativeKazhdanBound_distance
#print axioms ThomGame.Analysis.hilbertRelativeKazhdanBound_close_invariant
#print axioms ThomGame.Analysis.hilbertRelativeKazhdanBound_uniform_displacement
#print axioms ThomGame.Analysis.freeShear_inl_range_normal
#print axioms ThomGame.Analysis.freeShear_invariant_distance
#print axioms ThomGame.Analysis.freeShear_close_invariant
#print axioms ThomGame.Analysis.freeShear_lattice_uniform_displacement
#print axioms ThomGame.Analysis.rootPlane_pullback_lattice
#print axioms ThomGame.Analysis.rootPlane_invariant_distance
#print axioms ThomGame.Analysis.rootPlane_close_invariant
#print axioms ThomGame.Analysis.rootPlane_uniform_displacement
#print axioms ThomGame.Analysis.rootPlaneKazhdanGenerator_is_root
#print axioms ThomGame.Analysis.integralShear_root_uniform_displacement

#print axioms ThomGame.Analysis.mem_unitaryFixedSpace
#print axioms ThomGame.Analysis.unitaryFixedSpace_map
#print axioms ThomGame.Analysis.unitaryFixedSpace_projection_commute
#print axioms ThomGame.Analysis.unitaryFixedSpace_projection_apply
#print axioms ThomGame.Analysis.unitaryFixedSpace_projection_symm_apply
#print axioms ThomGame.Analysis.unitaryHeisenberg_projected_inverse_fixed
#print axioms ThomGame.Analysis.unitaryHeisenberg_translate_orthogonal
#print axioms ThomGame.Analysis.unitaryHeisenberg_angle_sq
#print axioms ThomGame.Analysis.unitaryHeisenberg_angle
#print axioms ThomGame.IntegralShear.mem_rootSubgroup
#print axioms ThomGame.IntegralShear.rootElement_mem_rootSubgroup
#print axioms ThomGame.IntegralShear.of_mem_rootSubgroup
#print axioms ThomGame.IntegralShear.rootHom_injective
#print axioms ThomGame.IntegralShear.rootSubgroup_abelian
#print axioms ThomGame.IntegralShear.rootSubgroup_commute
#print axioms ThomGame.IntegralShear.rootSubgroup_commutator
#print axioms ThomGame.IntegralShear.rootSubgroups_generate
#print axioms ThomGame.IntegralShear.rootPair_contains_center
#print axioms ThomGame.IntegralShear.of_heisenberg_relation
#print axioms ThomGame.Analysis.rootSubgroup_invariants_eq
#print axioms ThomGame.Analysis.rootPair_unitary_heisenberg_relation
#print axioms ThomGame.Analysis.rootPair_unitary_center_commute
#print axioms ThomGame.Analysis.integralRootPair_angle_sq
#print axioms ThomGame.Analysis.integralRootPair_angle
#print axioms ThomGame.Analysis.integralRootPair_sum_sq_le
#print axioms ThomGame.Analysis.integralRootPair_central_free_angle
#print axioms ThomGame.Analysis.integralRootPair_central_free_four_sum_sq_le
#print axioms ThomGame.Analysis.unitaryHeisenberg_mixed_fixed_orthogonal
#print axioms ThomGame.Analysis.hilbert_two_vector_sum_sq_le
#print axioms ThomGame.Analysis.unitaryHeisenberg_four_sum_sq_le
#print axioms ThomGame.Analysis.rootPairSubgroup_invariants_eq
#print axioms ThomGame.Analysis.integralRootPair_four_sum_sq_le

#print axioms ThomGame.IntegerRootGraph.reverse_reverse
#print axioms ThomGame.IntegerRootGraph.reverse_ne
#print axioms ThomGame.IntegerRootGraph.neighbor_reverse
#print axioms ThomGame.IntegerRootGraph.reverseIndex_reverseIndex
#print axioms ThomGame.IntegerRootGraph.neighbor_injective
#print axioms ThomGame.IntegerRootGraph.adjacent_iff_neighbor
#print axioms ThomGame.IntegerRootGraph.adjacent_iff_all_axes
#print axioms ThomGame.IntegerRootGraph.vertexEnumeration_bijective
#print axioms ThomGame.IntegerRootGraph.vertex_card
#print axioms ThomGame.IntegerRootGraph.directed_edge_card
#print axioms ThomGame.IntegerRootGraph.sum_neighbors_complement
#print axioms ThomGame.IntegerRootGraph.sum_neighbors_reindex
#print axioms ThomGame.IntegerRootGraph.sum_opposites_reindex
#print axioms ThomGame.Analysis.IntegerRootGraph.pullback_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.vertex_sum_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.constant_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.opposite_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.total_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_closed_form
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_operator_formula
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_opposite
#print axioms ThomGame.Analysis.IntegerRootGraph.opposite_opposite
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_constant
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_laplacian
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_constant
#print axioms ThomGame.Analysis.IntegerRootGraph.vertex_norm_sq
#print axioms ThomGame.Analysis.IntegerRootGraph.opposite_norm
#print axioms ThomGame.Analysis.IntegerRootGraph.opposite_inner
#print axioms ThomGame.Analysis.IntegerRootGraph.total_inner
#print axioms ThomGame.Analysis.IntegerRootGraph.edgeEnergy_nonneg
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_energy_expanded
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_energy
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_symmetric
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_nonneg
#print axioms ThomGame.Analysis.IntegerRootGraph.constant_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.mem_constantSpace
#print axioms ThomGame.Analysis.IntegerRootGraph.constantSpace_closed
#print axioms ThomGame.Analysis.IntegerRootGraph.mean_eq_constant
#print axioms ThomGame.Analysis.IntegerRootGraph.mean_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_mean
#print axioms ThomGame.Analysis.IntegerRootGraph.mean_constant
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_residual
#print axioms ThomGame.Analysis.IntegerRootGraph.constant_inner
#print axioms ThomGame.Analysis.IntegerRootGraph.constantSpace_orthogonal_iff
#print axioms ThomGame.Analysis.IntegerRootGraph.constantSpace_starProjection
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_mean
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_residual
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_zero_sum_formula
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_zero_sum_gap
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_zero_sum_norm_le
#print axioms ThomGame.Analysis.IntegerRootGraph.edgeEnergy_residual
#print axioms ThomGame.Analysis.IntegerRootGraph.graph_residual_gap
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_kernel
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_gap
#print axioms ThomGame.Analysis.IntegerRootGraph.green_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexSum_green
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_green
#print axioms ThomGame.Analysis.IntegerRootGraph.green_laplacian
#print axioms ThomGame.Analysis.IntegerRootGraph.green_norm_le
#print axioms ThomGame.IntegralShear.rootSubgroup_le_rootSpan
#print axioms ThomGame.IntegralShear.rootSpan_le
#print axioms ThomGame.IntegralShear.rootSpan_mono
#print axioms ThomGame.IntegralShear.graphEdgeRoots_subset_vertex
#print axioms ThomGame.IntegralShear.graphEdgeRoots_reverse
#print axioms ThomGame.IntegralShear.graphVertexGroup_contains_root
#print axioms ThomGame.IntegralShear.graphVertexGroup_eq_pair
#print axioms ThomGame.IntegralShear.graphEdgeGroup_reverse
#print axioms ThomGame.IntegralShear.graphEdgeGroup_le_vertex
#print axioms ThomGame.IntegralShear.graphEdgeGroup_le_neighbor
#print axioms ThomGame.IntegralShear.graphVertexGroups_generate
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexInvariants_le_edge
#print axioms ThomGame.Analysis.IntegerRootGraph.neighborInvariants_le_edge
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_closed
#print axioms ThomGame.Analysis.IntegerRootGraph.decompositionSpace_closed
#print axioms ThomGame.Analysis.IntegerRootGraph.constants_le_decomposition
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_le_decomposition
#print axioms ThomGame.Analysis.IntegerRootGraph.edgeDifference_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_edge_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.decompositionSpace_edge_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexInvariants_iInf
#print axioms ThomGame.Analysis.IntegerRootGraph.constant_mem_fixedFields_iff
#print axioms ThomGame.Analysis.IntegerRootGraph.constants_inf_fixedFields
#print axioms ThomGame.Analysis.IntegerRootGraph.projected_edgeDifference_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFieldProjection_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_starProjection
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.decomposition_projection_vertexSum
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_zero_sum
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_inner
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_norm_lower
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_energy_bound
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_unit_energy
#print axioms ThomGame.Analysis.IntegerRootGraph.four_vector_sum_norm_sq_le
#print axioms ThomGame.Analysis.IntegerRootGraph.laplacian_sum_edgeDifference
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_laplacian_norm_sq_le
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_project_compressed
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_vertex_energy_lower
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_unit_vertex_energy_lower
#print axioms ThomGame.Analysis.hilbert_coercive_norm_lower
#print axioms ThomGame.Analysis.hilbert_coercive_antilipschitz
#print axioms ThomGame.Analysis.hilbert_coercive_closed_range
#print axioms ThomGame.Analysis.hilbert_coercive_range_eq_top
#print axioms ThomGame.Analysis.hilbert_coercive_bijective
#print axioms ThomGame.Analysis.unitaryFixedSpace_projection_mem_of_mapsTo
#print axioms ThomGame.Analysis.unitaryHeisenberg_project_Y_eq_common
#print axioms ThomGame.Analysis.unitaryHeisenberg_project_X_eq_common
#print axioms ThomGame.Analysis.unitaryHeisenberg_triangle_residual_orthogonal
#print axioms ThomGame.Analysis.unitaryHeisenberg_triangle_energy
#print axioms ThomGame.Analysis.IntegerRootGraph.decompositionSpace_edge_root_fixed
#print axioms ThomGame.Analysis.IntegerRootGraph.vertexInvariants_across_eq_common
#print axioms ThomGame.Analysis.IntegerRootGraph.root_triangle_energy
#print axioms ThomGame.Analysis.IntegerRootGraph.sum_across_reindex
#print axioms ThomGame.Analysis.IntegerRootGraph.sum_right_reindex
#print axioms ThomGame.Analysis.IntegerRootGraph.four_nonneg_two_le_sum
#print axioms ThomGame.Analysis.IntegerRootGraph.edgeDifference_reverse
#print axioms ThomGame.Analysis.IntegerRootGraph.triangle_total_energy
#print axioms ThomGame.Analysis.IntegerRootGraph.triangle_vertex_energy_le
#print axioms ThomGame.Analysis.IntegerRootGraph.triangle_root_energy_le
#print axioms ThomGame.Analysis.IntegerRootGraph.technical_energy_bound
#print axioms ThomGame.Analysis.IntegerRootGraph.mem_zeroSumDecomposition
#print axioms ThomGame.Analysis.IntegerRootGraph.zeroSumDecomposition_closed
#print axioms ThomGame.Analysis.IntegerRootGraph.reducedLaplacian_apply
#print axioms ThomGame.Analysis.IntegerRootGraph.reducedLaplacian_coercive
#print axioms ThomGame.Analysis.IntegerRootGraph.reducedLaplacian_bijective
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_exists_unique
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_solution_bounds
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_unit_solution
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_three_energy_bounds

#print axioms ThomGame.Analysis.unitaryHeisenberg_common_le_center
#print axioms ThomGame.Analysis.unitaryHeisenberg_common_project_center
#print axioms ThomGame.Analysis.unitaryHeisenberg_mixed_residual_orthogonal
#print axioms ThomGame.Analysis.unitaryHeisenberg_central_sum_sq_le
#print axioms ThomGame.Analysis.unitaryHeisenberg_refined_four_sum
#print axioms ThomGame.Analysis.unitaryFixedSpace_residual_fixed
#print axioms ThomGame.Analysis.unitaryFixedSpace_orthogonal_residual
#print axioms ThomGame.Analysis.unitaryHeisenberg_projected_four_sum
#print axioms ThomGame.Analysis.IntegerRootGraph.four_sum_formula
#print axioms ThomGame.Analysis.IntegerRootGraph.root_vertex_four_sum_bound
#print axioms ThomGame.Analysis.IntegerRootGraph.vertex_laplacian_refined_bound
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_residual_norm_sq
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_residual_projection
#print axioms ThomGame.Analysis.IntegerRootGraph.compressedLaplacian_refined_bound
#print axioms ThomGame.Analysis.IntegerRootGraph.zeroSumDecomposition_complement_gap
#print axioms ThomGame.Analysis.IntegerRootGraph.zeroSumDecomposition_fixed_projection_lower_sq
#print axioms ThomGame.Analysis.IntegerRootGraph.zeroSumDecomposition_fixed_projection_lower
#print axioms ThomGame.Analysis.subspaceProjection_apply
#print axioms ThomGame.Analysis.subspaceProjection_surjective
#print axioms ThomGame.Analysis.subspaceProjection_lower_dual
#print axioms ThomGame.Analysis.IntegerRootGraph.decomposition_residual_mem
#print axioms ThomGame.Analysis.IntegerRootGraph.zeroSumDecomposition_le_constant_orthogonal
#print axioms ThomGame.Analysis.IntegerRootGraph.zeroSumDecomposition_starProjection
#print axioms ThomGame.Analysis.IntegerRootGraph.decomposition_orthogonal_zeroSum_mem_constant
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_inf_zeroSum_orthogonal
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_distance_to_constants
#print axioms ThomGame.Analysis.IntegerRootGraph.fixedFields_mean_gap
#print axioms ThomGame.Analysis.IntegerRootGraph.constants_distance_to_fixedFields
#print axioms ThomGame.Analysis.IntegerRootGraph.constant_norm_sq
#print axioms ThomGame.Analysis.IntegerRootGraph.vertex_invariant_distances_gap
#print axioms ThomGame.Analysis.unitaryFixedSpace_uniform_distance
#print axioms ThomGame.Analysis.unitaryHeisenberg_common_fixed_distance
#print axioms ThomGame.Analysis.integralShear_root_fixed_distance
#print axioms ThomGame.Analysis.integralShear_vertex_invariant_distance
#print axioms ThomGame.Analysis.integralShear_no_invariants_norm_le
#print axioms ThomGame.Analysis.hilbertUnitaryInvariantOrthogonal_stable
#print axioms ThomGame.Analysis.hilbertNonInvariantRepresentation_apply
#print axioms ThomGame.Analysis.hilbertNonInvariantRepresentation_invariants
#print axioms ThomGame.Analysis.integralShearKazhdanConstant_pos
#print axioms ThomGame.Analysis.of_mem_integralShearKazhdanSet
#print axioms ThomGame.Analysis.integralShear_orthogonal_norm_le
#print axioms ThomGame.Analysis.integralShear_hilbertKazhdanBound
#print axioms ThomGame.Analysis.integralShear_hasFiniteHilbertKazhdanSet
#print axioms ThomGame.Compressor.hasFiniteHilbertKazhdanSet
#print axioms ThomGame.Compressor.generatorKazhdanConstant_pos
#print axioms ThomGame.Compressor.generatorTuple_displacement
#print axioms ThomGame.Compressor.generatorTuple_energy
#print axioms ThomGame.Construction.compressor_Q_spectral_gap
#print axioms ThomGame.Construction.compressor_spectral_gaps
#print axioms ThomGame.Construction.compressor_internality
#print axioms ThomGame.Construction.lambda_matrix_J_eq_one
#print axioms ThomGame.Construction.lambdaApproximatelyTrivial
#print axioms ThomGame.Construction.sigmaApproximatelyTrivial
#print axioms ThomGame.Construction.sigmaApproximation_conclusion
#print axioms ThomGame.Construction.sigmaApproximation_hsNorm
#print axioms ThomGame.Construction.sigma_uniform_no_negative_J

#print axioms ThomGame.SparseSystem.RowPermutation.columns_perm
#print axioms ThomGame.SparseSystem.RowPermutation.matrix_eq
#print axioms ThomGame.SparseSystem.RowPermutation.satisfies_iff
#print axioms ThomGame.SparseSystem.mem_rowSupport
#print axioms ThomGame.SparseSystem.rowSupport_card
#print axioms ThomGame.SparseSystem.ordered_strictMono
#print axioms ThomGame.SparseSystem.ordered_matrix
#print axioms ThomGame.SparseSystem.ordered_rhs
#print axioms ThomGame.SparseSystem.ordered_column_mem
#print axioms ThomGame.SparseSystem.ordered_column_unique
#print axioms ThomGame.SolutionGroup.rowPermutationHom_J
#print axioms ThomGame.SolutionGroup.rowPermutationHom_x
#print axioms ThomGame.SolutionGroup.rowPermutationHom_comp
#print axioms ThomGame.SolutionGroup.rowPermutationEquiv_J
#print axioms ThomGame.SolutionGroup.rowPermutationEquiv_x
#print axioms ThomGame.Analysis.unitaryDist_swap
#print axioms ThomGame.Analysis.unitaryLength_commutator_swap
#print axioms ThomGame.Analysis.unitaryTriple_permutation_bound
#print axioms ThomGame.Analysis.unitaryTriple_perm_bound
#print axioms ThomGame.Analysis.assignment_word_eval
#print axioms ThomGame.Analysis.solution_approx_nonneg
#print axioms ThomGame.Analysis.solution_approx_commutator
#print axioms ThomGame.Analysis.solution_approx_row
#print axioms ThomGame.Analysis.solution_row_permutation_error
#print axioms ThomGame.Analysis.solution_approx_permute
#print axioms ThomGame.Analysis.solution_approximatelyTrivial_permute
#print axioms ThomGame.SolutionGroup.Paper.relators_finite
#print axioms ThomGame.SolutionGroup.Paper.eval_relation
#print axioms ThomGame.SolutionGroup.Paper.eval_commutator_eq_one_iff
#print axioms ThomGame.SolutionGroup.Paper.J_sq
#print axioms ThomGame.SolutionGroup.Paper.x_sq
#print axioms ThomGame.SolutionGroup.Paper.J_commutes_x
#print axioms ThomGame.SolutionGroup.Paper.row_commutes_lt
#print axioms ThomGame.SolutionGroup.Paper.row_commutes
#print axioms ThomGame.SolutionGroup.Paper.row_product
#print axioms ThomGame.SolutionGroup.Paper.model_eval_relation
#print axioms ThomGame.SolutionGroup.Paper.modelToHom_J
#print axioms ThomGame.SolutionGroup.Paper.modelToHom_x
#print axioms ThomGame.SolutionGroup.Paper.toSolution_J
#print axioms ThomGame.SolutionGroup.Paper.toSolution_x
#print axioms ThomGame.SolutionGroup.Paper.ofSolution_J
#print axioms ThomGame.SolutionGroup.Paper.ofSolution_x
#print axioms ThomGame.SolutionGroup.Paper.toSolution_comp_ofSolution
#print axioms ThomGame.SolutionGroup.Paper.ofSolution_comp_toSolution
#print axioms ThomGame.SolutionGroup.Paper.solutionEquiv_J
#print axioms ThomGame.SolutionGroup.Paper.solutionEquiv_x
#print axioms ThomGame.Analysis.assignment_commutator_swap
#print axioms ThomGame.Analysis.paper_approx_nonneg
#print axioms ThomGame.Analysis.paper_approx_to_solution
#print axioms ThomGame.Analysis.solution_approx_to_paper
#print axioms ThomGame.Analysis.paper_approx_iff_solution
#print axioms ThomGame.Analysis.paper_approximatelyTrivial_iff_solution
#print axioms ThomGame.Analysis.paper_ordered_approx_to_original
#print axioms ThomGame.Analysis.original_approx_to_paper_ordered
#print axioms ThomGame.Analysis.paper_ordered_approximatelyTrivial
#print axioms ThomGame.Construction.paperSystem_matrix
#print axioms ThomGame.Construction.paperSystem_rhs
#print axioms ThomGame.Construction.paperSystem_strictMono
#print axioms ThomGame.Construction.paperSystem_column_order
#print axioms ThomGame.Construction.paperSystem_support
#print axioms ThomGame.Construction.paperSystem_column_unique
#print axioms ThomGame.Construction.paperSystem_rhs_formula
#print axioms ThomGame.Construction.paperSigmaEquiv_J
#print axioms ThomGame.Construction.paperSigmaEquiv_x
#print axioms ThomGame.Construction.paper_relators_finite
#print axioms ThomGame.Construction.paper_J_sigma_ne_one
#print axioms ThomGame.Construction.paper_approx_to_engineering
#print axioms ThomGame.Construction.engineering_approx_to_paper
#print axioms ThomGame.Construction.paperSigmaApproximatelyTrivial
#print axioms ThomGame.Construction.paperApproximation_conclusion
#print axioms ThomGame.Construction.paperApproximation_hsNorm
#print axioms ThomGame.Construction.paper_uniform_no_negative_J

#print axioms ThomGame.Quantum.ProjectiveMeasurement.apply_twice
#print axioms ThomGame.Quantum.ProjectiveMeasurement.sum_apply
#print axioms ThomGame.Quantum.ProjectiveMeasurement.norm_sq_apply
#print axioms ThomGame.Quantum.ProjectiveMeasurement.sum_norm_sq
#print axioms ThomGame.Quantum.ProjectiveMeasurement.apply_norm_sq_le
#print axioms ThomGame.Quantum.ProjectiveMeasurement.inner_apply_eq_zero
#print axioms ThomGame.Quantum.ProjectiveMeasurement.deterministic_apply
#print axioms ThomGame.Quantum.IsProbabilityTable.le_one
#print axioms ThomGame.Quantum.continuous_table_entry
#print axioms ThomGame.Quantum.isClosed_probabilityTables
#print axioms ThomGame.Quantum.isClosed_noSignalling
#print axioms ThomGame.Quantum.CommutingStrategy.correlation_nonneg
#print axioms ThomGame.Quantum.CommutingStrategy.apply_commute
#print axioms ThomGame.Quantum.CommutingStrategy.correlation_inner
#print axioms ThomGame.Quantum.CommutingStrategy.bob_marginal
#print axioms ThomGame.Quantum.CommutingStrategy.alice_marginal
#print axioms ThomGame.Quantum.CommutingStrategy.correlation_normalized
#print axioms ThomGame.Quantum.CommutingStrategy.isProbabilityTable
#print axioms ThomGame.Quantum.CommutingStrategy.noSignalling
#print axioms ThomGame.Quantum.CommutingStrategy.correlation_le_one
#print axioms ThomGame.Quantum.ProjectiveMeasurement.tensorLeft_tmul
#print axioms ThomGame.Quantum.ProjectiveMeasurement.tensorRight_tmul
#print axioms ThomGame.Quantum.ProjectiveMeasurement.tensor_commute
#print axioms ThomGame.Quantum.FiniteStrategy.correlation_born
#print axioms ThomGame.Quantum.FiniteStrategy.isProbabilityTable
#print axioms ThomGame.Quantum.FiniteStrategy.noSignalling
#print axioms ThomGame.Quantum.FiniteStrategy.deterministic_correlation
#print axioms ThomGame.Quantum.FiniteGame.answerScore_nonneg
#print axioms ThomGame.Quantum.FiniteGame.answerScore_le_one
#print axioms ThomGame.Quantum.FiniteGame.success_nonneg
#print axioms ThomGame.Quantum.FiniteGame.success_le_one
#print axioms ThomGame.Quantum.FiniteGame.continuous_success
#print axioms ThomGame.Quantum.FiniteGame.success_add
#print axioms ThomGame.Quantum.FiniteGame.success_smul
#print axioms ThomGame.Quantum.quantumCorrelation_isProbabilityTable
#print axioms ThomGame.Quantum.quantumCorrelation_noSignalling
#print axioms ThomGame.Quantum.approximateQuantumCorrelation_isProbabilityTable
#print axioms ThomGame.Quantum.approximateQuantumCorrelation_noSignalling
#print axioms ThomGame.Quantum.commutingCorrelation_isProbabilityTable
#print axioms ThomGame.Quantum.commutingCorrelation_noSignalling
#print axioms ThomGame.Quantum.quantum_subset_approximateQuantum
#print axioms ThomGame.Quantum.quantum_subset_commuting
#print axioms ThomGame.Quantum.quantumCorrelations_nonempty
#print axioms ThomGame.Quantum.approximateQuantumCorrelations_nonempty
#print axioms ThomGame.Quantum.commutingCorrelations_nonempty
#print axioms ThomGame.Quantum.FiniteGame.success_bddAbove
#print axioms ThomGame.Quantum.FiniteGame.success_le_value
#print axioms ThomGame.Quantum.FiniteGame.value_le_one
#print axioms ThomGame.Quantum.FiniteGame.value_nonneg
#print axioms ThomGame.Quantum.FiniteGame.value_closure
#print axioms ThomGame.Quantum.FiniteGame.omegaQ_eq_omegaQa
#print axioms ThomGame.Quantum.FiniteGame.omegaQ_le_one
#print axioms ThomGame.Quantum.FiniteGame.omegaQa_le_one
#print axioms ThomGame.Quantum.FiniteGame.omegaQc_le_one
#print axioms ThomGame.Quantum.FiniteGame.omegaQ_nonneg
#print axioms ThomGame.Quantum.FiniteGame.omegaQa_nonneg
#print axioms ThomGame.Quantum.FiniteGame.omegaQc_nonneg
#print axioms ThomGame.Quantum.FiniteGame.omegaQ_le_omegaQc
#print axioms ThomGame.Quantum.FiniteGame.finiteStrategy_success_le
#print axioms ThomGame.Quantum.FiniteGame.commutingStrategy_success_le
#print axioms ThomGame.Quantum.FiniteGame.omegaQ_eq_one_iff
#print axioms ThomGame.Quantum.FiniteGame.omegaQ_lt_one_of_uniform_gap
#print axioms ThomGame.Quantum.FiniteGame.omegaQc_eq_one_of_perfect
#print axioms ThomGame.SparseSystem.sum_rowSupport
#print axioms ThomGame.SparseSystem.incidenceWeight_nonneg
#print axioms ThomGame.SparseSystem.incidenceWeight_sum
#print axioms ThomGame.SparseSystem.incidencePayoff_nonneg
#print axioms ThomGame.SparseSystem.incidencePayoff_le_one
#print axioms ThomGame.SparseSystem.incidenceGame_weight
#print axioms ThomGame.SparseSystem.incidenceGame_payoff
#print axioms ThomGame.SparseSystem.incidenceGame_success
#print axioms ThomGame.SparseSystem.incidenceGame_perfect_of_zero_rejected
#print axioms ThomGame.Construction.paperGame_weight
#print axioms ThomGame.Construction.paperGame_payoff
#print axioms ThomGame.Construction.paperGame_success
#print axioms ThomGame.Construction.paperGame_answer_counts
#print axioms ThomGame.Construction.paper_omegaQ_eq_omegaQa
#print axioms ThomGame.Construction.paper_values_bounds
#print axioms ThomGame.Construction.paper_omegaQ_eq_one_iff

#print axioms ThomGame.Quantum.GroupHilbert.permute_apply
#print axioms ThomGame.Quantum.GroupHilbert.permute_delta
#print axioms ThomGame.Quantum.GroupHilbert.delta_norm
#print axioms ThomGame.Quantum.GroupHilbert.delta_inner
#print axioms ThomGame.Quantum.GroupHilbert.left_apply
#print axioms ThomGame.Quantum.GroupHilbert.right_apply
#print axioms ThomGame.Quantum.GroupHilbert.left_one
#print axioms ThomGame.Quantum.GroupHilbert.right_one
#print axioms ThomGame.Quantum.GroupHilbert.left_mul
#print axioms ThomGame.Quantum.GroupHilbert.right_mul
#print axioms ThomGame.Quantum.GroupHilbert.left_right_commute
#print axioms ThomGame.Quantum.GroupHilbert.left_delta
#print axioms ThomGame.Quantum.GroupHilbert.right_delta
#print axioms ThomGame.Quantum.GroupHilbert.left_inner
#print axioms ThomGame.Quantum.GroupHilbert.right_inner
#print axioms ThomGame.Quantum.GroupHilbert.left_square
#print axioms ThomGame.Quantum.GroupHilbert.right_square
#print axioms ThomGame.Quantum.GroupHilbert.left_selfAdjoint
#print axioms ThomGame.Quantum.GroupHilbert.right_selfAdjoint
#print axioms ThomGame.Quantum.GroupHilbert.centralState_norm_sq
#print axioms ThomGame.Quantum.GroupHilbert.centralState_norm
#print axioms ThomGame.Quantum.GroupHilbert.left_centralState
#print axioms ThomGame.Quantum.GroupHilbert.left_right_centralState
#print axioms ThomGame.Quantum.bit_cases
#print axioms ThomGame.Quantum.bitSign_zero
#print axioms ThomGame.Quantum.bitSign_one
#print axioms ThomGame.Quantum.bitSign_add
#print axioms ThomGame.Quantum.bitSign_sq
#print axioms ThomGame.Quantum.bitSign_injective
#print axioms ThomGame.Quantum.bitSign_selfAdjoint
#print axioms ThomGame.Quantum.bitProjection_selfAdjoint
#print axioms ThomGame.Quantum.bitProjection_idempotent
#print axioms ThomGame.Quantum.bitProjection_orthogonal
#print axioms ThomGame.Quantum.bitProjection_sum
#print axioms ThomGame.Quantum.bitProjection_eigen
#print axioms ThomGame.Quantum.bitProjection_commute
#print axioms ThomGame.Quantum.bitProjections_commute
#print axioms ThomGame.Quantum.ProjectiveMeasurement.cross_product
#print axioms ThomGame.Quantum.ProjectiveMeasurement.joint_proj
#print axioms ThomGame.Quantum.tripleMeasurement_proj
#print axioms ThomGame.Quantum.tripleMeasurement_commute
#print axioms ThomGame.Quantum.tripleMeasurement_eigen
#print axioms ThomGame.Quantum.tripleMeasurement_product_eigen
#print axioms ThomGame.Quantum.LinearSystemObservables.alice_commute_left
#print axioms ThomGame.Quantum.LinearSystemObservables.alice_commute_right
#print axioms ThomGame.Quantum.LinearSystemObservables.alice_eigen
#print axioms ThomGame.Quantum.LinearSystemObservables.alice_product_eigen
#print axioms ThomGame.Quantum.LinearSystemObservables.alice_bob_commute
#print axioms ThomGame.Quantum.LinearSystemObservables.outcome_commute_left
#print axioms ThomGame.Quantum.LinearSystemObservables.outcome_commute_right
#print axioms ThomGame.Quantum.LinearSystemObservables.outcome_eigen_left
#print axioms ThomGame.Quantum.LinearSystemObservables.outcome_eigen_right
#print axioms ThomGame.Quantum.LinearSystemObservables.zero_of_distinct_bits
#print axioms ThomGame.Quantum.LinearSystemObservables.outcome_zero_of_inconsistent
#print axioms ThomGame.Quantum.LinearSystemObservables.outcome_zero_of_wrong_parity
#print axioms ThomGame.Quantum.LinearSystemObservables.rejected_probability_zero
#print axioms ThomGame.Quantum.LinearSystemObservables.perfect_success
#print axioms ThomGame.Quantum.regularSolutionStrategy_state
#print axioms ThomGame.Quantum.regularSolutionStrategy_born
#print axioms ThomGame.Quantum.regularSolutionStrategy_rejected_zero
#print axioms ThomGame.Quantum.regularSolutionStrategy_perfect
#print axioms ThomGame.Construction.paperCommutingStrategy_state
#print axioms ThomGame.Construction.paperCommutingStrategy_rejected_zero
#print axioms ThomGame.Construction.paperCommutingStrategy_perfect
#print axioms ThomGame.Construction.paper_omegaQc_eq_one
#print axioms ThomGame.Construction.paper_values_with_perfect_commuting

#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_one
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_const
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_sub
#print axioms ThomGame.Quantum.ProjectiveMeasurement.proj_eval
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_proj
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_mul
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_commute
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_selfAdjoint
#print axioms ThomGame.Quantum.ProjectiveMeasurement.eval_norm_sq
#print axioms ThomGame.Quantum.ProjectiveMeasurement.joint_eval_left
#print axioms ThomGame.Quantum.ProjectiveMeasurement.joint_eval_right
#print axioms ThomGame.Quantum.bitSign_norm
#print axioms ThomGame.Quantum.bitSign_sub_norm_sq
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_selfAdjoint
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_square
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_commute
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_mul
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_triple
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_norm
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_sub_sign_norm_sq
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_cross_commute
#print axioms ThomGame.Quantum.ProjectiveMeasurement.observable_difference_norm_sq
#print axioms ThomGame.SparseSystem.rejection_nonneg
#print axioms ThomGame.SparseSystem.rejection_eq_one_sub
#print axioms ThomGame.SparseSystem.sum_rejection_eq_loss
#print axioms ThomGame.SparseSystem.rejection_le_loss
#print axioms ThomGame.SparseSystem.inconsistency_le_rejection
#print axioms ThomGame.SparseSystem.wrong_parity_le_rejection
#print axioms ThomGame.Quantum.CommutingStrategy.aliceBit_selfAdjoint
#print axioms ThomGame.Quantum.CommutingStrategy.bobBit_selfAdjoint
#print axioms ThomGame.Quantum.CommutingStrategy.aliceBit_square
#print axioms ThomGame.Quantum.CommutingStrategy.bobBit_square
#print axioms ThomGame.Quantum.CommutingStrategy.aliceBit_commute
#print axioms ThomGame.Quantum.CommutingStrategy.bit_cross_commute
#print axioms ThomGame.Quantum.CommutingStrategy.aliceBit_norm
#print axioms ThomGame.Quantum.CommutingStrategy.bobBit_norm
#print axioms ThomGame.Quantum.CommutingStrategy.aliceBit_product
#print axioms ThomGame.Quantum.CommutingStrategy.consistency_error_sq
#print axioms ThomGame.Quantum.CommutingStrategy.parity_error_sq
#print axioms ThomGame.Quantum.CommutingStrategy.consistency_error_sq_le_loss
#print axioms ThomGame.Quantum.CommutingStrategy.parity_error_sq_le_loss
#print axioms ThomGame.Quantum.pair_state_transfer
#print axioms ThomGame.Quantum.triple_state_transfer
#print axioms ThomGame.Quantum.CommutingStrategy.bob_pair_state_transfer
#print axioms ThomGame.Quantum.CommutingStrategy.bob_triple_state_transfer
#print axioms ThomGame.Quantum.CommutingStrategy.incidenceError_nonneg
#print axioms ThomGame.Quantum.CommutingStrategy.incidenceError_sq
#print axioms ThomGame.Quantum.CommutingStrategy.consistency_error_le
#print axioms ThomGame.Quantum.CommutingStrategy.parity_error_le
#print axioms ThomGame.Quantum.CommutingStrategy.bob_row_error_le
#print axioms ThomGame.Quantum.CommutingStrategy.bob_commutator_error_le
#print axioms ThomGame.Quantum.CommutingStrategy.incidenceError_le_of_near_perfect
#print axioms ThomGame.Quantum.CommutingStrategy.near_perfect_state_relations
#print axioms ThomGame.Quantum.ProjectiveMeasurement.tensorLeft_observable
#print axioms ThomGame.Quantum.ProjectiveMeasurement.tensorRight_observable
#print axioms ThomGame.Quantum.FiniteStrategy.toCommuting_state
#print axioms ThomGame.Quantum.FiniteStrategy.localAliceBit_selfAdjoint
#print axioms ThomGame.Quantum.FiniteStrategy.localBobBit_selfAdjoint
#print axioms ThomGame.Quantum.FiniteStrategy.localAliceBit_square
#print axioms ThomGame.Quantum.FiniteStrategy.localBobBit_square
#print axioms ThomGame.Quantum.FiniteStrategy.localAliceBit_commute
#print axioms ThomGame.Quantum.FiniteStrategy.toCommuting_aliceBit
#print axioms ThomGame.Quantum.FiniteStrategy.toCommuting_bobBit
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_local_consistency
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_local_row
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_local_commutator
#print axioms ThomGame.Construction.paper_finite_strategy_consistency
#print axioms ThomGame.Construction.paper_finite_strategy_row
#print axioms ThomGame.Construction.paper_finite_strategy_commutator

#print axioms ThomGame.Quantum.localMatrix_apply
#print axioms ThomGame.Quantum.localMatrix_mul
#print axioms ThomGame.Quantum.localMatrix_one
#print axioms ThomGame.Quantum.localMatrix_sub
#print axioms ThomGame.Quantum.localMatrix_smul
#print axioms ThomGame.Quantum.localMatrix_star
#print axioms ThomGame.Quantum.localMatrix_isHermitian
#print axioms ThomGame.Quantum.localMatrix_apply_vector
#print axioms ThomGame.Quantum.tensorStateMatrix_tmul
#print axioms ThomGame.Quantum.tensorStateMatrix_norm
#print axioms ThomGame.Quantum.tensorStateMatrix_bob
#print axioms ThomGame.Quantum.tensorStateMatrix_alice
#print axioms ThomGame.Quantum.tensorStateMatrix_consistency_norm
#print axioms ThomGame.Quantum.tensorStateMatrix_bob_norm
#print axioms ThomGame.Quantum.tensorStateMatrix_bob_sub_smul_norm
#print axioms ThomGame.Analysis.matrixRectAbs_unitary_mul
#print axioms ThomGame.Analysis.matrixRectAbs_mul_unitary
#print axioms ThomGame.Analysis.rectHSNorm_right_density_commutator_le
#print axioms ThomGame.Analysis.rectHSNorm_left_density_commutator_le
#print axioms ThomGame.Analysis.rectHSNorm_mul_left_density
#print axioms ThomGame.Quantum.reducedDensity_nonneg
#print axioms ThomGame.Quantum.densityRoot_nonneg
#print axioms ThomGame.Quantum.densityRoot_sq
#print axioms ThomGame.Quantum.densityRoot_sqrt
#print axioms ThomGame.Quantum.densityRoot_norm
#print axioms ThomGame.Quantum.reducedDensity_trace
#print axioms ThomGame.Quantum.densityRoot_weighted_norm
#print axioms ThomGame.Quantum.densityRoot_weighted_sub_smul_norm
#print axioms ThomGame.Quantum.densityRoot_commutator_le
#print axioms ThomGame.Quantum.FiniteStrategy.bobUnitary_val
#print axioms ThomGame.Quantum.FiniteStrategy.bobMatrix_isHermitian
#print axioms ThomGame.Quantum.FiniteStrategy.bobMatrix_square
#print axioms ThomGame.Quantum.FiniteStrategy.state_densityRoot_norm
#print axioms ThomGame.Quantum.FiniteStrategy.state_reducedDensity_trace
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_density_commutator
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_density_row
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_density_relation_commutator
#print axioms ThomGame.Analysis.weighted_abs_product_sum_sq_le
#print axioms ThomGame.Analysis.weighted_square_difference_sum_le
#print axioms ThomGame.Analysis.weighted_squareSteps_integrable
#print axioms ThomGame.Analysis.weighted_squareSteps_integral
#print axioms ThomGame.Analysis.weighted_squareSteps_coarea
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_eq_sqrt_cut
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_isStarProjection
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_intertwiner_sq
#print axioms ThomGame.Analysis.matrixIntertwiner_plus_spectral_sq
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_intertwiner_integrable
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_intertwiner_coarea
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_unitary_coarea
#print axioms ThomGame.Analysis.spectralStep_positive_indicator
#print axioms ThomGame.Analysis.spectralStep_square_integrableOn
#print axioms ThomGame.Analysis.spectralStep_square_integral
#print axioms ThomGame.Analysis.rectHSNorm_right_cfc_sq
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_weighted_sq
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_weighted_integrableOn
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_weighted_integral
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_mass_integral
#print axioms ThomGame.Analysis.exists_positive_mass_threshold
#print axioms ThomGame.Analysis.matrixCutError_nonneg
#print axioms ThomGame.Analysis.matrixCutError_generator_le
#print axioms ThomGame.Analysis.matrixCutError_relation_le
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_error_integrableOn
#print axioms ThomGame.Analysis.matrixSquareSpectralCut_error_integral_le
#print axioms ThomGame.Analysis.exists_common_matrixSpectralCut
#print axioms ThomGame.Quantum.systemDensityBudget_pos
#print axioms ThomGame.Quantum.FiniteStrategy.relationMatrix_weighted_norm_le
#print axioms ThomGame.Quantum.FiniteStrategy.total_density_error_le
#print axioms ThomGame.Quantum.FiniteStrategy.near_perfect_common_spectralCut
#print axioms ThomGame.Quantum.continuous_systemDensityBudget
#print axioms ThomGame.Quantum.systemDensityBudget_zero
#print axioms ThomGame.Quantum.exists_small_positive_densityBudget
#print axioms ThomGame.SparseSystem.near_perfect_common_projection
#print axioms ThomGame.Construction.paper_near_perfect_projection

#print axioms ThomGame.Analysis.matrixFrame_range_mul
#print axioms ThomGame.Analysis.rectHSNorm_mul_frame_le
#print axioms ThomGame.Analysis.rectHSNorm_mul_frame_le_cut
#print axioms ThomGame.Analysis.matrixFrame_leakage_gram
#print axioms ThomGame.Analysis.matrixFrame_leakage_eq
#print axioms ThomGame.Analysis.matrixFrame_leakage_le
#print axioms ThomGame.Analysis.exists_matrixCompression_unitary
#print axioms ThomGame.Analysis.rectHSNorm_neg
#print axioms ThomGame.Analysis.matrixIntertwiningError_nonneg
#print axioms ThomGame.Analysis.matrixIntertwiningError_one
#print axioms ThomGame.Analysis.matrixIntertwiningError_mul_le
#print axioms ThomGame.Analysis.matrixIntertwiningError_inv
#print axioms ThomGame.Analysis.matrixIntertwiningError_triple_le
#print axioms ThomGame.Analysis.matrixIntertwiningError_relation_le
#print axioms ThomGame.Analysis.matrixIntertwiningError_difference_le
#print axioms ThomGame.Analysis.rectHSNorm_projection_rank
#print axioms ThomGame.Analysis.rectHSNorm_normalization_sq
#print axioms ThomGame.Analysis.rectHSNorm_rank_le_of_relative
#print axioms ThomGame.SparseSystem.near_perfect_unitary_relations
#print axioms ThomGame.Analysis.negativeCentralAssignment_none
#print axioms ThomGame.Analysis.negativeCentralAssignment_some
#print axioms ThomGame.Analysis.negativeCentralAssignment_row
#print axioms ThomGame.Analysis.negativeCentralAssignment_rhs_val
#print axioms ThomGame.Analysis.negativeCentralAssignment_isApprox
#print axioms ThomGame.SparseSystem.near_perfect_approximation
#print axioms ThomGame.SparseSystem.uniform_gap_of_no_negative_J
#print axioms ThomGame.SparseSystem.omegaQ_lt_one_of_no_negative_J
#print axioms ThomGame.SparseSystem.omegaQ_lt_one_of_approximatelyTrivial
#print axioms ThomGame.Construction.paper_near_perfect_approximation
#print axioms ThomGame.Construction.paper_uniform_quantum_gap
#print axioms ThomGame.Construction.paper_omegaQ_lt_one
#print axioms ThomGame.Construction.paper_omegaQa_lt_one
#print axioms ThomGame.Construction.paper_quantum_value_separation
#print axioms ThomGame.Construction.paper_main_results
