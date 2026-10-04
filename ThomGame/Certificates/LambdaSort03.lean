module

public import ThomGame.Certificates.LambdaSort04

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_003_length : input_003.length = 1929 := by
  simp only [input_003, List.length_append, input_004_length, input_035_length]

theorem sort_003_correct :
    KernelSort.sortFuel wordLE 15434 input_003 = output_003 := by
  exact KernelSort.sortFuel_step wordLE 15433 964 965
    input_004 input_035 output_004 output_035 output_003
    input_004_length input_035_length (by decide) (by decide)
    sort_004_correct sort_035_correct (by decide +kernel)

theorem input_066_length : input_066.length = 1930 := by
  simp only [input_066, List.length_append, input_067_length, input_098_length]

theorem sort_066_correct :
    KernelSort.sortFuel wordLE 15434 input_066 = output_066 := by
  exact KernelSort.sortFuel_step wordLE 15433 965 965
    input_067 input_098 output_067 output_098 output_066
    input_067_length input_098_length (by decide) (by decide)
    sort_067_correct sort_098_correct (by decide +kernel)

theorem input_130_length : input_130.length = 1929 := by
  simp only [input_130, List.length_append, input_131_length, input_162_length]

theorem sort_130_correct :
    KernelSort.sortFuel wordLE 15434 input_130 = output_130 := by
  exact KernelSort.sortFuel_step wordLE 15433 964 965
    input_131 input_162 output_131 output_162 output_130
    input_131_length input_162_length (by decide) (by decide)
    sort_131_correct sort_162_correct (by decide +kernel)

theorem input_193_length : input_193.length = 1930 := by
  simp only [input_193, List.length_append, input_194_length, input_225_length]

theorem sort_193_correct :
    KernelSort.sortFuel wordLE 15434 input_193 = output_193 := by
  exact KernelSort.sortFuel_step wordLE 15433 965 965
    input_194 input_225 output_194 output_225 output_193
    input_194_length input_225_length (by decide) (by decide)
    sort_194_correct sort_225_correct (by decide +kernel)

theorem input_258_length : input_258.length = 1929 := by
  simp only [input_258, List.length_append, input_259_length, input_290_length]

theorem sort_258_correct :
    KernelSort.sortFuel wordLE 15434 input_258 = output_258 := by
  exact KernelSort.sortFuel_step wordLE 15433 964 965
    input_259 input_290 output_259 output_290 output_258
    input_259_length input_290_length (by decide) (by decide)
    sort_259_correct sort_290_correct (by decide +kernel)

theorem input_321_length : input_321.length = 1930 := by
  simp only [input_321, List.length_append, input_322_length, input_353_length]

theorem sort_321_correct :
    KernelSort.sortFuel wordLE 15434 input_321 = output_321 := by
  exact KernelSort.sortFuel_step wordLE 15433 965 965
    input_322 input_353 output_322 output_353 output_321
    input_322_length input_353_length (by decide) (by decide)
    sort_322_correct sort_353_correct (by decide +kernel)

theorem input_385_length : input_385.length = 1930 := by
  simp only [input_385, List.length_append, input_386_length, input_417_length]

theorem sort_385_correct :
    KernelSort.sortFuel wordLE 15434 input_385 = output_385 := by
  exact KernelSort.sortFuel_step wordLE 15433 965 965
    input_386 input_417 output_386 output_417 output_385
    input_386_length input_417_length (by decide) (by decide)
    sort_386_correct sort_417_correct (by decide +kernel)

theorem input_448_length : input_448.length = 1930 := by
  simp only [input_448, List.length_append, input_449_length, input_480_length]

theorem sort_448_correct :
    KernelSort.sortFuel wordLE 15434 input_448 = output_448 := by
  exact KernelSort.sortFuel_step wordLE 15433 965 965
    input_449 input_480 output_449 output_480 output_448
    input_449_length input_480_length (by decide) (by decide)
    sort_449_correct sort_480_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
