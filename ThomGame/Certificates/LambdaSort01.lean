module

public import ThomGame.Certificates.LambdaSort02

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_001_length : input_001.length = 7718 := by
  simp only [input_001, List.length_append, input_002_length, input_129_length]

theorem sort_001_correct :
    KernelSort.sortFuel wordLE 15436 input_001 = output_001 := by
  exact KernelSort.sortFuel_step wordLE 15435 3859 3859
    input_002 input_129 output_002 output_129 output_001
    input_002_length input_129_length (by decide) (by decide)
    sort_002_correct sort_129_correct (by decide +kernel)

theorem input_256_length : input_256.length = 7719 := by
  simp only [input_256, List.length_append, input_257_length, input_384_length]

theorem sort_256_correct :
    KernelSort.sortFuel wordLE 15436 input_256 = output_256 := by
  exact KernelSort.sortFuel_step wordLE 15435 3859 3860
    input_257 input_384 output_257 output_384 output_256
    input_257_length input_384_length (by decide) (by decide)
    sort_257_correct sort_384_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
