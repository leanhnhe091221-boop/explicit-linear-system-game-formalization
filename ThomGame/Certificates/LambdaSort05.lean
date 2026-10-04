module

public import ThomGame.Certificates.LambdaSort06

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_005_length : input_005.length = 482 := by
  simp only [input_005, List.length_append, input_006_length, input_013_length]

theorem sort_005_correct :
    KernelSort.sortFuel wordLE 15432 input_005 = output_005 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_006 input_013 output_006 output_013 output_005
    input_006_length input_013_length (by decide) (by decide)
    sort_006_correct sort_013_correct (by decide +kernel)

theorem input_020_length : input_020.length = 482 := by
  simp only [input_020, List.length_append, input_021_length, input_028_length]

theorem sort_020_correct :
    KernelSort.sortFuel wordLE 15432 input_020 = output_020 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_021 input_028 output_021 output_028 output_020
    input_021_length input_028_length (by decide) (by decide)
    sort_021_correct sort_028_correct (by decide +kernel)

theorem input_036_length : input_036.length = 482 := by
  simp only [input_036, List.length_append, input_037_length, input_044_length]

theorem sort_036_correct :
    KernelSort.sortFuel wordLE 15432 input_036 = output_036 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_037 input_044 output_037 output_044 output_036
    input_037_length input_044_length (by decide) (by decide)
    sort_037_correct sort_044_correct (by decide +kernel)

theorem input_051_length : input_051.length = 483 := by
  simp only [input_051, List.length_append, input_052_length, input_059_length]

theorem sort_051_correct :
    KernelSort.sortFuel wordLE 15432 input_051 = output_051 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_052 input_059 output_052 output_059 output_051
    input_052_length input_059_length (by decide) (by decide)
    sort_052_correct sort_059_correct (by decide +kernel)

theorem input_068_length : input_068.length = 482 := by
  simp only [input_068, List.length_append, input_069_length, input_076_length]

theorem sort_068_correct :
    KernelSort.sortFuel wordLE 15432 input_068 = output_068 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_069 input_076 output_069 output_076 output_068
    input_069_length input_076_length (by decide) (by decide)
    sort_069_correct sort_076_correct (by decide +kernel)

theorem input_083_length : input_083.length = 483 := by
  simp only [input_083, List.length_append, input_084_length, input_091_length]

theorem sort_083_correct :
    KernelSort.sortFuel wordLE 15432 input_083 = output_083 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_084 input_091 output_084 output_091 output_083
    input_084_length input_091_length (by decide) (by decide)
    sort_084_correct sort_091_correct (by decide +kernel)

theorem input_099_length : input_099.length = 482 := by
  simp only [input_099, List.length_append, input_100_length, input_107_length]

theorem sort_099_correct :
    KernelSort.sortFuel wordLE 15432 input_099 = output_099 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_100 input_107 output_100 output_107 output_099
    input_100_length input_107_length (by decide) (by decide)
    sort_100_correct sort_107_correct (by decide +kernel)

theorem input_114_length : input_114.length = 483 := by
  simp only [input_114, List.length_append, input_115_length, input_122_length]

theorem sort_114_correct :
    KernelSort.sortFuel wordLE 15432 input_114 = output_114 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_115 input_122 output_115 output_122 output_114
    input_115_length input_122_length (by decide) (by decide)
    sort_115_correct sort_122_correct (by decide +kernel)

theorem input_132_length : input_132.length = 482 := by
  simp only [input_132, List.length_append, input_133_length, input_140_length]

theorem sort_132_correct :
    KernelSort.sortFuel wordLE 15432 input_132 = output_132 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_133 input_140 output_133 output_140 output_132
    input_133_length input_140_length (by decide) (by decide)
    sort_133_correct sort_140_correct (by decide +kernel)

theorem input_147_length : input_147.length = 482 := by
  simp only [input_147, List.length_append, input_148_length, input_155_length]

theorem sort_147_correct :
    KernelSort.sortFuel wordLE 15432 input_147 = output_147 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_148 input_155 output_148 output_155 output_147
    input_148_length input_155_length (by decide) (by decide)
    sort_148_correct sort_155_correct (by decide +kernel)

theorem input_163_length : input_163.length = 482 := by
  simp only [input_163, List.length_append, input_164_length, input_171_length]

theorem sort_163_correct :
    KernelSort.sortFuel wordLE 15432 input_163 = output_163 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_164 input_171 output_164 output_171 output_163
    input_164_length input_171_length (by decide) (by decide)
    sort_164_correct sort_171_correct (by decide +kernel)

theorem input_178_length : input_178.length = 483 := by
  simp only [input_178, List.length_append, input_179_length, input_186_length]

theorem sort_178_correct :
    KernelSort.sortFuel wordLE 15432 input_178 = output_178 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_179 input_186 output_179 output_186 output_178
    input_179_length input_186_length (by decide) (by decide)
    sort_179_correct sort_186_correct (by decide +kernel)

theorem input_195_length : input_195.length = 482 := by
  simp only [input_195, List.length_append, input_196_length, input_203_length]

theorem sort_195_correct :
    KernelSort.sortFuel wordLE 15432 input_195 = output_195 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_196 input_203 output_196 output_203 output_195
    input_196_length input_203_length (by decide) (by decide)
    sort_196_correct sort_203_correct (by decide +kernel)

theorem input_210_length : input_210.length = 483 := by
  simp only [input_210, List.length_append, input_211_length, input_218_length]

theorem sort_210_correct :
    KernelSort.sortFuel wordLE 15432 input_210 = output_210 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_211 input_218 output_211 output_218 output_210
    input_211_length input_218_length (by decide) (by decide)
    sort_211_correct sort_218_correct (by decide +kernel)

theorem input_226_length : input_226.length = 482 := by
  simp only [input_226, List.length_append, input_227_length, input_234_length]

theorem sort_226_correct :
    KernelSort.sortFuel wordLE 15432 input_226 = output_226 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_227 input_234 output_227 output_234 output_226
    input_227_length input_234_length (by decide) (by decide)
    sort_227_correct sort_234_correct (by decide +kernel)

theorem input_241_length : input_241.length = 483 := by
  simp only [input_241, List.length_append, input_242_length, input_249_length]

theorem sort_241_correct :
    KernelSort.sortFuel wordLE 15432 input_241 = output_241 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_242 input_249 output_242 output_249 output_241
    input_242_length input_249_length (by decide) (by decide)
    sort_242_correct sort_249_correct (by decide +kernel)

theorem input_260_length : input_260.length = 482 := by
  simp only [input_260, List.length_append, input_261_length, input_268_length]

theorem sort_260_correct :
    KernelSort.sortFuel wordLE 15432 input_260 = output_260 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_261 input_268 output_261 output_268 output_260
    input_261_length input_268_length (by decide) (by decide)
    sort_261_correct sort_268_correct (by decide +kernel)

theorem input_275_length : input_275.length = 482 := by
  simp only [input_275, List.length_append, input_276_length, input_283_length]

theorem sort_275_correct :
    KernelSort.sortFuel wordLE 15432 input_275 = output_275 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_276 input_283 output_276 output_283 output_275
    input_276_length input_283_length (by decide) (by decide)
    sort_276_correct sort_283_correct (by decide +kernel)

theorem input_291_length : input_291.length = 482 := by
  simp only [input_291, List.length_append, input_292_length, input_299_length]

theorem sort_291_correct :
    KernelSort.sortFuel wordLE 15432 input_291 = output_291 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_292 input_299 output_292 output_299 output_291
    input_292_length input_299_length (by decide) (by decide)
    sort_292_correct sort_299_correct (by decide +kernel)

theorem input_306_length : input_306.length = 483 := by
  simp only [input_306, List.length_append, input_307_length, input_314_length]

theorem sort_306_correct :
    KernelSort.sortFuel wordLE 15432 input_306 = output_306 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_307 input_314 output_307 output_314 output_306
    input_307_length input_314_length (by decide) (by decide)
    sort_307_correct sort_314_correct (by decide +kernel)

theorem input_323_length : input_323.length = 482 := by
  simp only [input_323, List.length_append, input_324_length, input_331_length]

theorem sort_323_correct :
    KernelSort.sortFuel wordLE 15432 input_323 = output_323 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_324 input_331 output_324 output_331 output_323
    input_324_length input_331_length (by decide) (by decide)
    sort_324_correct sort_331_correct (by decide +kernel)

theorem input_338_length : input_338.length = 483 := by
  simp only [input_338, List.length_append, input_339_length, input_346_length]

theorem sort_338_correct :
    KernelSort.sortFuel wordLE 15432 input_338 = output_338 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_339 input_346 output_339 output_346 output_338
    input_339_length input_346_length (by decide) (by decide)
    sort_339_correct sort_346_correct (by decide +kernel)

theorem input_354_length : input_354.length = 482 := by
  simp only [input_354, List.length_append, input_355_length, input_362_length]

theorem sort_354_correct :
    KernelSort.sortFuel wordLE 15432 input_354 = output_354 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_355 input_362 output_355 output_362 output_354
    input_355_length input_362_length (by decide) (by decide)
    sort_355_correct sort_362_correct (by decide +kernel)

theorem input_369_length : input_369.length = 483 := by
  simp only [input_369, List.length_append, input_370_length, input_377_length]

theorem sort_369_correct :
    KernelSort.sortFuel wordLE 15432 input_369 = output_369 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_370 input_377 output_370 output_377 output_369
    input_370_length input_377_length (by decide) (by decide)
    sort_370_correct sort_377_correct (by decide +kernel)

theorem input_387_length : input_387.length = 482 := by
  simp only [input_387, List.length_append, input_388_length, input_395_length]

theorem sort_387_correct :
    KernelSort.sortFuel wordLE 15432 input_387 = output_387 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_388 input_395 output_388 output_395 output_387
    input_388_length input_395_length (by decide) (by decide)
    sort_388_correct sort_395_correct (by decide +kernel)

theorem input_402_length : input_402.length = 483 := by
  simp only [input_402, List.length_append, input_403_length, input_410_length]

theorem sort_402_correct :
    KernelSort.sortFuel wordLE 15432 input_402 = output_402 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_403 input_410 output_403 output_410 output_402
    input_403_length input_410_length (by decide) (by decide)
    sort_403_correct sort_410_correct (by decide +kernel)

theorem input_418_length : input_418.length = 482 := by
  simp only [input_418, List.length_append, input_419_length, input_426_length]

theorem sort_418_correct :
    KernelSort.sortFuel wordLE 15432 input_418 = output_418 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_419 input_426 output_419 output_426 output_418
    input_419_length input_426_length (by decide) (by decide)
    sort_419_correct sort_426_correct (by decide +kernel)

theorem input_433_length : input_433.length = 483 := by
  simp only [input_433, List.length_append, input_434_length, input_441_length]

theorem sort_433_correct :
    KernelSort.sortFuel wordLE 15432 input_433 = output_433 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_434 input_441 output_434 output_441 output_433
    input_434_length input_441_length (by decide) (by decide)
    sort_434_correct sort_441_correct (by decide +kernel)

theorem input_450_length : input_450.length = 482 := by
  simp only [input_450, List.length_append, input_451_length, input_458_length]

theorem sort_450_correct :
    KernelSort.sortFuel wordLE 15432 input_450 = output_450 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_451 input_458 output_451 output_458 output_450
    input_451_length input_458_length (by decide) (by decide)
    sort_451_correct sort_458_correct (by decide +kernel)

theorem input_465_length : input_465.length = 483 := by
  simp only [input_465, List.length_append, input_466_length, input_473_length]

theorem sort_465_correct :
    KernelSort.sortFuel wordLE 15432 input_465 = output_465 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_466 input_473 output_466 output_473 output_465
    input_466_length input_473_length (by decide) (by decide)
    sort_466_correct sort_473_correct (by decide +kernel)

theorem input_481_length : input_481.length = 482 := by
  simp only [input_481, List.length_append, input_482_length, input_489_length]

theorem sort_481_correct :
    KernelSort.sortFuel wordLE 15432 input_481 = output_481 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 241
    input_482 input_489 output_482 output_489 output_481
    input_482_length input_489_length (by decide) (by decide)
    sort_482_correct sort_489_correct (by decide +kernel)

theorem input_496_length : input_496.length = 483 := by
  simp only [input_496, List.length_append, input_497_length, input_504_length]

theorem sort_496_correct :
    KernelSort.sortFuel wordLE 15432 input_496 = output_496 := by
  exact KernelSort.sortFuel_step wordLE 15431 241 242
    input_497 input_504 output_497 output_504 output_496
    input_497_length input_504_length (by decide) (by decide)
    sort_497_correct sort_504_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
