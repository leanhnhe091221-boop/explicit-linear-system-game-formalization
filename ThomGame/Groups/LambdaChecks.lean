module

public import ThomGame.Certificates.LambdaNormalized

/-!
# Counts of the canonical presentation

The checked chunk and merge certificates identify the actual normalization
program with a candidate table. Only the final table counts are computed here.
-/

@[expose] public section

namespace ThomGame.Lambda

set_option maxRecDepth 60000 in
set_option maxHeartbeats 12000000 in
theorem normalized_relator_count : normalizedRelators.length = 12863 := by
  rw [Certificate.normalized_eq_table]
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 12000000 in
theorem normalized_relator_total_length :
    (normalizedRelators.map List.length).sum = 118095 := by
  rw [Certificate.normalized_eq_table]
  decide +kernel

end ThomGame.Lambda
