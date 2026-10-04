module

public import ThomGame.Certificates.LambdaRawData

/-! Exact equality of the candidate table with the typed relation generator. -/

@[expose] public section
namespace ThomGame.Lambda.Certificate

set_option maxRecDepth 60000 in
set_option maxHeartbeats 12000000 in
theorem raw_eq_table : rawRelators = rawTable := by decide +kernel

end ThomGame.Lambda.Certificate
