module

public import ThomGame.Certificates.LambdaSort03

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_002_length : input_002.length = 3859 := by
  simp only [input_002, List.length_append, input_003_length, input_066_length]

theorem sort_002_correct :
    KernelSort.sortFuel wordLE 15435 input_002 = output_002 := by
  exact KernelSort.sortFuel_step wordLE 15434 1929 1930
    input_003 input_066 output_003 output_066 output_002
    input_003_length input_066_length (by decide) (by decide)
    sort_003_correct sort_066_correct (by decide +kernel)

theorem input_129_length : input_129.length = 3859 := by
  simp only [input_129, List.length_append, input_130_length, input_193_length]

theorem sort_129_correct :
    KernelSort.sortFuel wordLE 15435 input_129 = output_129 := by
  exact KernelSort.sortFuel_step wordLE 15434 1929 1930
    input_130 input_193 output_130 output_193 output_129
    input_130_length input_193_length (by decide) (by decide)
    sort_130_correct sort_193_correct (by decide +kernel)

theorem input_257_length : input_257.length = 3859 := by
  simp only [input_257, List.length_append, input_258_length, input_321_length]

theorem sort_257_correct :
    KernelSort.sortFuel wordLE 15435 input_257 = output_257 := by
  exact KernelSort.sortFuel_step wordLE 15434 1929 1930
    input_258 input_321 output_258 output_321 output_257
    input_258_length input_321_length (by decide) (by decide)
    sort_258_correct sort_321_correct (by decide +kernel)

theorem input_384_length : input_384.length = 3860 := by
  simp only [input_384, List.length_append, input_385_length, input_448_length]

theorem sort_384_correct :
    KernelSort.sortFuel wordLE 15435 input_384 = output_384 := by
  exact KernelSort.sortFuel_step wordLE 15434 1930 1930
    input_385 input_448 output_385 output_448 output_384
    input_385_length input_448_length (by decide) (by decide)
    sort_385_correct sort_448_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
