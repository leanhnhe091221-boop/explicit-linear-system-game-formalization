module

public import ThomGame.Certificates.LambdaCanonical
public import ThomGame.Certificates.LambdaSort00

/-! The normalization program equals the fully checked candidate table. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_table_eq_sort_input : cleanTable = input_000 := by decide +kernel

theorem output_eraseReps : output_000.eraseReps = normalizedTable := by decide +kernel

theorem normalized_eq_table : normalizedRelators = normalizedTable := by
  rw [normalizedRelators, clean_eq_table, clean_table_eq_sort_input]
  change (KernelSort.sort wordLE input_000).eraseReps = normalizedTable
  rw [KernelSort.sort, input_000_length, sort_000_correct, output_eraseReps]

end ThomGame.Lambda.Certificate
