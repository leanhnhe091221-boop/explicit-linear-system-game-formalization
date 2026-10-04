module

public import ThomGame.Certificates.LambdaSort01

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_000_length : input_000.length = 15437 := by
  simp only [input_000, List.length_append, input_001_length, input_256_length]

theorem sort_000_correct :
    KernelSort.sortFuel wordLE 15437 input_000 = output_000 := by
  exact KernelSort.sortFuel_step wordLE 15436 7718 7719
    input_001 input_256 output_001 output_256 output_000
    input_001_length input_256_length (by decide) (by decide)
    sort_001_correct sort_256_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
