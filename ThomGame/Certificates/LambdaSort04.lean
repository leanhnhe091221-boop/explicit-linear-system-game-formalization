module

public import ThomGame.Certificates.LambdaSort05

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_004_length : input_004.length = 964 := by
  simp only [input_004, List.length_append, input_005_length, input_020_length]

theorem sort_004_correct :
    KernelSort.sortFuel wordLE 15433 input_004 = output_004 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 482
    input_005 input_020 output_005 output_020 output_004
    input_005_length input_020_length (by decide) (by decide)
    sort_005_correct sort_020_correct (by decide +kernel)

theorem input_035_length : input_035.length = 965 := by
  simp only [input_035, List.length_append, input_036_length, input_051_length]

theorem sort_035_correct :
    KernelSort.sortFuel wordLE 15433 input_035 = output_035 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_036 input_051 output_036 output_051 output_035
    input_036_length input_051_length (by decide) (by decide)
    sort_036_correct sort_051_correct (by decide +kernel)

theorem input_067_length : input_067.length = 965 := by
  simp only [input_067, List.length_append, input_068_length, input_083_length]

theorem sort_067_correct :
    KernelSort.sortFuel wordLE 15433 input_067 = output_067 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_068 input_083 output_068 output_083 output_067
    input_068_length input_083_length (by decide) (by decide)
    sort_068_correct sort_083_correct (by decide +kernel)

theorem input_098_length : input_098.length = 965 := by
  simp only [input_098, List.length_append, input_099_length, input_114_length]

theorem sort_098_correct :
    KernelSort.sortFuel wordLE 15433 input_098 = output_098 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_099 input_114 output_099 output_114 output_098
    input_099_length input_114_length (by decide) (by decide)
    sort_099_correct sort_114_correct (by decide +kernel)

theorem input_131_length : input_131.length = 964 := by
  simp only [input_131, List.length_append, input_132_length, input_147_length]

theorem sort_131_correct :
    KernelSort.sortFuel wordLE 15433 input_131 = output_131 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 482
    input_132 input_147 output_132 output_147 output_131
    input_132_length input_147_length (by decide) (by decide)
    sort_132_correct sort_147_correct (by decide +kernel)

theorem input_162_length : input_162.length = 965 := by
  simp only [input_162, List.length_append, input_163_length, input_178_length]

theorem sort_162_correct :
    KernelSort.sortFuel wordLE 15433 input_162 = output_162 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_163 input_178 output_163 output_178 output_162
    input_163_length input_178_length (by decide) (by decide)
    sort_163_correct sort_178_correct (by decide +kernel)

theorem input_194_length : input_194.length = 965 := by
  simp only [input_194, List.length_append, input_195_length, input_210_length]

theorem sort_194_correct :
    KernelSort.sortFuel wordLE 15433 input_194 = output_194 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_195 input_210 output_195 output_210 output_194
    input_195_length input_210_length (by decide) (by decide)
    sort_195_correct sort_210_correct (by decide +kernel)

theorem input_225_length : input_225.length = 965 := by
  simp only [input_225, List.length_append, input_226_length, input_241_length]

theorem sort_225_correct :
    KernelSort.sortFuel wordLE 15433 input_225 = output_225 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_226 input_241 output_226 output_241 output_225
    input_226_length input_241_length (by decide) (by decide)
    sort_226_correct sort_241_correct (by decide +kernel)

theorem input_259_length : input_259.length = 964 := by
  simp only [input_259, List.length_append, input_260_length, input_275_length]

theorem sort_259_correct :
    KernelSort.sortFuel wordLE 15433 input_259 = output_259 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 482
    input_260 input_275 output_260 output_275 output_259
    input_260_length input_275_length (by decide) (by decide)
    sort_260_correct sort_275_correct (by decide +kernel)

theorem input_290_length : input_290.length = 965 := by
  simp only [input_290, List.length_append, input_291_length, input_306_length]

theorem sort_290_correct :
    KernelSort.sortFuel wordLE 15433 input_290 = output_290 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_291 input_306 output_291 output_306 output_290
    input_291_length input_306_length (by decide) (by decide)
    sort_291_correct sort_306_correct (by decide +kernel)

theorem input_322_length : input_322.length = 965 := by
  simp only [input_322, List.length_append, input_323_length, input_338_length]

theorem sort_322_correct :
    KernelSort.sortFuel wordLE 15433 input_322 = output_322 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_323 input_338 output_323 output_338 output_322
    input_323_length input_338_length (by decide) (by decide)
    sort_323_correct sort_338_correct (by decide +kernel)

theorem input_353_length : input_353.length = 965 := by
  simp only [input_353, List.length_append, input_354_length, input_369_length]

theorem sort_353_correct :
    KernelSort.sortFuel wordLE 15433 input_353 = output_353 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_354 input_369 output_354 output_369 output_353
    input_354_length input_369_length (by decide) (by decide)
    sort_354_correct sort_369_correct (by decide +kernel)

theorem input_386_length : input_386.length = 965 := by
  simp only [input_386, List.length_append, input_387_length, input_402_length]

theorem sort_386_correct :
    KernelSort.sortFuel wordLE 15433 input_386 = output_386 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_387 input_402 output_387 output_402 output_386
    input_387_length input_402_length (by decide) (by decide)
    sort_387_correct sort_402_correct (by decide +kernel)

theorem input_417_length : input_417.length = 965 := by
  simp only [input_417, List.length_append, input_418_length, input_433_length]

theorem sort_417_correct :
    KernelSort.sortFuel wordLE 15433 input_417 = output_417 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_418 input_433 output_418 output_433 output_417
    input_418_length input_433_length (by decide) (by decide)
    sort_418_correct sort_433_correct (by decide +kernel)

theorem input_449_length : input_449.length = 965 := by
  simp only [input_449, List.length_append, input_450_length, input_465_length]

theorem sort_449_correct :
    KernelSort.sortFuel wordLE 15433 input_449 = output_449 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_450 input_465 output_450 output_465 output_449
    input_450_length input_465_length (by decide) (by decide)
    sort_450_correct sort_465_correct (by decide +kernel)

theorem input_480_length : input_480.length = 965 := by
  simp only [input_480, List.length_append, input_481_length, input_496_length]

theorem sort_480_correct :
    KernelSort.sortFuel wordLE 15433 input_480 = output_480 := by
  exact KernelSort.sortFuel_step wordLE 15432 482 483
    input_481 input_496 output_481 output_496 output_480
    input_481_length input_496_length (by decide) (by decide)
    sort_481_correct sort_496_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
