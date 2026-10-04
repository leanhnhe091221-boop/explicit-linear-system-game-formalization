module

public import ThomGame.Groups.CompressorPresentation

/-!
# Kernel-checked finite counts for Q

The propositions below evaluate the actual typed relation generator.
They do not rely on the Python manifest or on native evaluation axioms.
-/

@[expose] public section

namespace ThomGame.Compressor

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem family_counts :
    [e0.length, e1.length, e2e3.length, e4.length, shearComm.length,
      shearRoot.length, shearTorsion.length, actionRelations.length, negativeRecovery.length] =
    [42, 882, 84, 6174, 18, 6, 1, 504, 18] := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem raw_relator_count : rawRelators.length = 7729 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem raw_relator_total_length : (rawRelators.map List.length).sum = 68712 := by decide +kernel

theorem generator_number_in_range :
    ∀ g : Generator, 1 ≤ generatorNumber g ∧ generatorNumber g ≤ 48 := by decide

theorem generator_number_injective : Function.Injective generatorNumber := by decide

end ThomGame.Compressor
