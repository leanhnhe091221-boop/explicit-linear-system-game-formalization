module

public import ThomGame.Certificates.LambdaSort07

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_006_length : input_006.length = 241 := by
  simp only [input_006, List.length_append, input_007_length, input_010_length]

theorem sort_006_correct :
    KernelSort.sortFuel wordLE 15431 input_006 = output_006 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_007 input_010 output_007 output_010 output_006
    input_007_length input_010_length (by decide) (by decide)
    sort_007_correct sort_010_correct (by decide +kernel)

theorem input_013_length : input_013.length = 241 := by
  simp only [input_013, List.length_append, input_014_length, input_017_length]

theorem sort_013_correct :
    KernelSort.sortFuel wordLE 15431 input_013 = output_013 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_014 input_017 output_014 output_017 output_013
    input_014_length input_017_length (by decide) (by decide)
    sort_014_correct sort_017_correct (by decide +kernel)

theorem input_021_length : input_021.length = 241 := by
  simp only [input_021, List.length_append, input_022_length, input_025_length]

theorem sort_021_correct :
    KernelSort.sortFuel wordLE 15431 input_021 = output_021 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_022 input_025 output_022 output_025 output_021
    input_022_length input_025_length (by decide) (by decide)
    sort_022_correct sort_025_correct (by decide +kernel)

theorem input_028_length : input_028.length = 241 := by
  simp only [input_028, List.length_append, input_029_length, input_032_length]

theorem sort_028_correct :
    KernelSort.sortFuel wordLE 15431 input_028 = output_028 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_029 input_032 output_029 output_032 output_028
    input_029_length input_032_length (by decide) (by decide)
    sort_029_correct sort_032_correct (by decide +kernel)

theorem input_037_length : input_037.length = 241 := by
  simp only [input_037, List.length_append, input_038_length, input_041_length]

theorem sort_037_correct :
    KernelSort.sortFuel wordLE 15431 input_037 = output_037 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_038 input_041 output_038 output_041 output_037
    input_038_length input_041_length (by decide) (by decide)
    sort_038_correct sort_041_correct (by decide +kernel)

theorem input_044_length : input_044.length = 241 := by
  simp only [input_044, List.length_append, input_045_length, input_048_length]

theorem sort_044_correct :
    KernelSort.sortFuel wordLE 15431 input_044 = output_044 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_045 input_048 output_045 output_048 output_044
    input_045_length input_048_length (by decide) (by decide)
    sort_045_correct sort_048_correct (by decide +kernel)

theorem input_052_length : input_052.length = 241 := by
  simp only [input_052, List.length_append, input_053_length, input_056_length]

theorem sort_052_correct :
    KernelSort.sortFuel wordLE 15431 input_052 = output_052 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_053 input_056 output_053 output_056 output_052
    input_053_length input_056_length (by decide) (by decide)
    sort_053_correct sort_056_correct (by decide +kernel)

theorem input_059_length : input_059.length = 242 := by
  simp only [input_059, List.length_append, input_060_length, input_063_length]

theorem sort_059_correct :
    KernelSort.sortFuel wordLE 15431 input_059 = output_059 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_060 input_063 output_060 output_063 output_059
    input_060_length input_063_length (by decide) (by decide)
    sort_060_correct sort_063_correct (by decide +kernel)

theorem input_069_length : input_069.length = 241 := by
  simp only [input_069, List.length_append, input_070_length, input_073_length]

theorem sort_069_correct :
    KernelSort.sortFuel wordLE 15431 input_069 = output_069 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_070 input_073 output_070 output_073 output_069
    input_070_length input_073_length (by decide) (by decide)
    sort_070_correct sort_073_correct (by decide +kernel)

theorem input_076_length : input_076.length = 241 := by
  simp only [input_076, List.length_append, input_077_length, input_080_length]

theorem sort_076_correct :
    KernelSort.sortFuel wordLE 15431 input_076 = output_076 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_077 input_080 output_077 output_080 output_076
    input_077_length input_080_length (by decide) (by decide)
    sort_077_correct sort_080_correct (by decide +kernel)

theorem input_084_length : input_084.length = 241 := by
  simp only [input_084, List.length_append, input_085_length, input_088_length]

theorem sort_084_correct :
    KernelSort.sortFuel wordLE 15431 input_084 = output_084 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_085 input_088 output_085 output_088 output_084
    input_085_length input_088_length (by decide) (by decide)
    sort_085_correct sort_088_correct (by decide +kernel)

theorem input_091_length : input_091.length = 242 := by
  simp only [input_091, List.length_append, input_092_length, input_095_length]

theorem sort_091_correct :
    KernelSort.sortFuel wordLE 15431 input_091 = output_091 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_092 input_095 output_092 output_095 output_091
    input_092_length input_095_length (by decide) (by decide)
    sort_092_correct sort_095_correct (by decide +kernel)

theorem input_100_length : input_100.length = 241 := by
  simp only [input_100, List.length_append, input_101_length, input_104_length]

theorem sort_100_correct :
    KernelSort.sortFuel wordLE 15431 input_100 = output_100 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_101 input_104 output_101 output_104 output_100
    input_101_length input_104_length (by decide) (by decide)
    sort_101_correct sort_104_correct (by decide +kernel)

theorem input_107_length : input_107.length = 241 := by
  simp only [input_107, List.length_append, input_108_length, input_111_length]

theorem sort_107_correct :
    KernelSort.sortFuel wordLE 15431 input_107 = output_107 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_108 input_111 output_108 output_111 output_107
    input_108_length input_111_length (by decide) (by decide)
    sort_108_correct sort_111_correct (by decide +kernel)

theorem input_115_length : input_115.length = 241 := by
  simp only [input_115, List.length_append, input_116_length, input_119_length]

theorem sort_115_correct :
    KernelSort.sortFuel wordLE 15431 input_115 = output_115 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_116 input_119 output_116 output_119 output_115
    input_116_length input_119_length (by decide) (by decide)
    sort_116_correct sort_119_correct (by decide +kernel)

theorem input_122_length : input_122.length = 242 := by
  simp only [input_122, List.length_append, input_123_length, input_126_length]

theorem sort_122_correct :
    KernelSort.sortFuel wordLE 15431 input_122 = output_122 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_123 input_126 output_123 output_126 output_122
    input_123_length input_126_length (by decide) (by decide)
    sort_123_correct sort_126_correct (by decide +kernel)

theorem input_133_length : input_133.length = 241 := by
  simp only [input_133, List.length_append, input_134_length, input_137_length]

theorem sort_133_correct :
    KernelSort.sortFuel wordLE 15431 input_133 = output_133 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_134 input_137 output_134 output_137 output_133
    input_134_length input_137_length (by decide) (by decide)
    sort_134_correct sort_137_correct (by decide +kernel)

theorem input_140_length : input_140.length = 241 := by
  simp only [input_140, List.length_append, input_141_length, input_144_length]

theorem sort_140_correct :
    KernelSort.sortFuel wordLE 15431 input_140 = output_140 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_141 input_144 output_141 output_144 output_140
    input_141_length input_144_length (by decide) (by decide)
    sort_141_correct sort_144_correct (by decide +kernel)

theorem input_148_length : input_148.length = 241 := by
  simp only [input_148, List.length_append, input_149_length, input_152_length]

theorem sort_148_correct :
    KernelSort.sortFuel wordLE 15431 input_148 = output_148 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_149 input_152 output_149 output_152 output_148
    input_149_length input_152_length (by decide) (by decide)
    sort_149_correct sort_152_correct (by decide +kernel)

theorem input_155_length : input_155.length = 241 := by
  simp only [input_155, List.length_append, input_156_length, input_159_length]

theorem sort_155_correct :
    KernelSort.sortFuel wordLE 15431 input_155 = output_155 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_156 input_159 output_156 output_159 output_155
    input_156_length input_159_length (by decide) (by decide)
    sort_156_correct sort_159_correct (by decide +kernel)

theorem input_164_length : input_164.length = 241 := by
  simp only [input_164, List.length_append, input_165_length, input_168_length]

theorem sort_164_correct :
    KernelSort.sortFuel wordLE 15431 input_164 = output_164 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_165 input_168 output_165 output_168 output_164
    input_165_length input_168_length (by decide) (by decide)
    sort_165_correct sort_168_correct (by decide +kernel)

theorem input_171_length : input_171.length = 241 := by
  simp only [input_171, List.length_append, input_172_length, input_175_length]

theorem sort_171_correct :
    KernelSort.sortFuel wordLE 15431 input_171 = output_171 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_172 input_175 output_172 output_175 output_171
    input_172_length input_175_length (by decide) (by decide)
    sort_172_correct sort_175_correct (by decide +kernel)

theorem input_179_length : input_179.length = 241 := by
  simp only [input_179, List.length_append, input_180_length, input_183_length]

theorem sort_179_correct :
    KernelSort.sortFuel wordLE 15431 input_179 = output_179 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_180 input_183 output_180 output_183 output_179
    input_180_length input_183_length (by decide) (by decide)
    sort_180_correct sort_183_correct (by decide +kernel)

theorem input_186_length : input_186.length = 242 := by
  simp only [input_186, List.length_append, input_187_length, input_190_length]

theorem sort_186_correct :
    KernelSort.sortFuel wordLE 15431 input_186 = output_186 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_187 input_190 output_187 output_190 output_186
    input_187_length input_190_length (by decide) (by decide)
    sort_187_correct sort_190_correct (by decide +kernel)

theorem input_196_length : input_196.length = 241 := by
  simp only [input_196, List.length_append, input_197_length, input_200_length]

theorem sort_196_correct :
    KernelSort.sortFuel wordLE 15431 input_196 = output_196 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_197 input_200 output_197 output_200 output_196
    input_197_length input_200_length (by decide) (by decide)
    sort_197_correct sort_200_correct (by decide +kernel)

theorem input_203_length : input_203.length = 241 := by
  simp only [input_203, List.length_append, input_204_length, input_207_length]

theorem sort_203_correct :
    KernelSort.sortFuel wordLE 15431 input_203 = output_203 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_204 input_207 output_204 output_207 output_203
    input_204_length input_207_length (by decide) (by decide)
    sort_204_correct sort_207_correct (by decide +kernel)

theorem input_211_length : input_211.length = 241 := by
  simp only [input_211, List.length_append, input_212_length, input_215_length]

theorem sort_211_correct :
    KernelSort.sortFuel wordLE 15431 input_211 = output_211 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_212 input_215 output_212 output_215 output_211
    input_212_length input_215_length (by decide) (by decide)
    sort_212_correct sort_215_correct (by decide +kernel)

theorem input_218_length : input_218.length = 242 := by
  simp only [input_218, List.length_append, input_219_length, input_222_length]

theorem sort_218_correct :
    KernelSort.sortFuel wordLE 15431 input_218 = output_218 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_219 input_222 output_219 output_222 output_218
    input_219_length input_222_length (by decide) (by decide)
    sort_219_correct sort_222_correct (by decide +kernel)

theorem input_227_length : input_227.length = 241 := by
  simp only [input_227, List.length_append, input_228_length, input_231_length]

theorem sort_227_correct :
    KernelSort.sortFuel wordLE 15431 input_227 = output_227 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_228 input_231 output_228 output_231 output_227
    input_228_length input_231_length (by decide) (by decide)
    sort_228_correct sort_231_correct (by decide +kernel)

theorem input_234_length : input_234.length = 241 := by
  simp only [input_234, List.length_append, input_235_length, input_238_length]

theorem sort_234_correct :
    KernelSort.sortFuel wordLE 15431 input_234 = output_234 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_235 input_238 output_235 output_238 output_234
    input_235_length input_238_length (by decide) (by decide)
    sort_235_correct sort_238_correct (by decide +kernel)

theorem input_242_length : input_242.length = 241 := by
  simp only [input_242, List.length_append, input_243_length, input_246_length]

theorem sort_242_correct :
    KernelSort.sortFuel wordLE 15431 input_242 = output_242 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_243 input_246 output_243 output_246 output_242
    input_243_length input_246_length (by decide) (by decide)
    sort_243_correct sort_246_correct (by decide +kernel)

theorem input_249_length : input_249.length = 242 := by
  simp only [input_249, List.length_append, input_250_length, input_253_length]

theorem sort_249_correct :
    KernelSort.sortFuel wordLE 15431 input_249 = output_249 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_250 input_253 output_250 output_253 output_249
    input_250_length input_253_length (by decide) (by decide)
    sort_250_correct sort_253_correct (by decide +kernel)

theorem input_261_length : input_261.length = 241 := by
  simp only [input_261, List.length_append, input_262_length, input_265_length]

theorem sort_261_correct :
    KernelSort.sortFuel wordLE 15431 input_261 = output_261 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_262 input_265 output_262 output_265 output_261
    input_262_length input_265_length (by decide) (by decide)
    sort_262_correct sort_265_correct (by decide +kernel)

theorem input_268_length : input_268.length = 241 := by
  simp only [input_268, List.length_append, input_269_length, input_272_length]

theorem sort_268_correct :
    KernelSort.sortFuel wordLE 15431 input_268 = output_268 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_269 input_272 output_269 output_272 output_268
    input_269_length input_272_length (by decide) (by decide)
    sort_269_correct sort_272_correct (by decide +kernel)

theorem input_276_length : input_276.length = 241 := by
  simp only [input_276, List.length_append, input_277_length, input_280_length]

theorem sort_276_correct :
    KernelSort.sortFuel wordLE 15431 input_276 = output_276 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_277 input_280 output_277 output_280 output_276
    input_277_length input_280_length (by decide) (by decide)
    sort_277_correct sort_280_correct (by decide +kernel)

theorem input_283_length : input_283.length = 241 := by
  simp only [input_283, List.length_append, input_284_length, input_287_length]

theorem sort_283_correct :
    KernelSort.sortFuel wordLE 15431 input_283 = output_283 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_284 input_287 output_284 output_287 output_283
    input_284_length input_287_length (by decide) (by decide)
    sort_284_correct sort_287_correct (by decide +kernel)

theorem input_292_length : input_292.length = 241 := by
  simp only [input_292, List.length_append, input_293_length, input_296_length]

theorem sort_292_correct :
    KernelSort.sortFuel wordLE 15431 input_292 = output_292 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_293 input_296 output_293 output_296 output_292
    input_293_length input_296_length (by decide) (by decide)
    sort_293_correct sort_296_correct (by decide +kernel)

theorem input_299_length : input_299.length = 241 := by
  simp only [input_299, List.length_append, input_300_length, input_303_length]

theorem sort_299_correct :
    KernelSort.sortFuel wordLE 15431 input_299 = output_299 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_300 input_303 output_300 output_303 output_299
    input_300_length input_303_length (by decide) (by decide)
    sort_300_correct sort_303_correct (by decide +kernel)

theorem input_307_length : input_307.length = 241 := by
  simp only [input_307, List.length_append, input_308_length, input_311_length]

theorem sort_307_correct :
    KernelSort.sortFuel wordLE 15431 input_307 = output_307 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_308 input_311 output_308 output_311 output_307
    input_308_length input_311_length (by decide) (by decide)
    sort_308_correct sort_311_correct (by decide +kernel)

theorem input_314_length : input_314.length = 242 := by
  simp only [input_314, List.length_append, input_315_length, input_318_length]

theorem sort_314_correct :
    KernelSort.sortFuel wordLE 15431 input_314 = output_314 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_315 input_318 output_315 output_318 output_314
    input_315_length input_318_length (by decide) (by decide)
    sort_315_correct sort_318_correct (by decide +kernel)

theorem input_324_length : input_324.length = 241 := by
  simp only [input_324, List.length_append, input_325_length, input_328_length]

theorem sort_324_correct :
    KernelSort.sortFuel wordLE 15431 input_324 = output_324 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_325 input_328 output_325 output_328 output_324
    input_325_length input_328_length (by decide) (by decide)
    sort_325_correct sort_328_correct (by decide +kernel)

theorem input_331_length : input_331.length = 241 := by
  simp only [input_331, List.length_append, input_332_length, input_335_length]

theorem sort_331_correct :
    KernelSort.sortFuel wordLE 15431 input_331 = output_331 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_332 input_335 output_332 output_335 output_331
    input_332_length input_335_length (by decide) (by decide)
    sort_332_correct sort_335_correct (by decide +kernel)

theorem input_339_length : input_339.length = 241 := by
  simp only [input_339, List.length_append, input_340_length, input_343_length]

theorem sort_339_correct :
    KernelSort.sortFuel wordLE 15431 input_339 = output_339 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_340 input_343 output_340 output_343 output_339
    input_340_length input_343_length (by decide) (by decide)
    sort_340_correct sort_343_correct (by decide +kernel)

theorem input_346_length : input_346.length = 242 := by
  simp only [input_346, List.length_append, input_347_length, input_350_length]

theorem sort_346_correct :
    KernelSort.sortFuel wordLE 15431 input_346 = output_346 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_347 input_350 output_347 output_350 output_346
    input_347_length input_350_length (by decide) (by decide)
    sort_347_correct sort_350_correct (by decide +kernel)

theorem input_355_length : input_355.length = 241 := by
  simp only [input_355, List.length_append, input_356_length, input_359_length]

theorem sort_355_correct :
    KernelSort.sortFuel wordLE 15431 input_355 = output_355 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_356 input_359 output_356 output_359 output_355
    input_356_length input_359_length (by decide) (by decide)
    sort_356_correct sort_359_correct (by decide +kernel)

theorem input_362_length : input_362.length = 241 := by
  simp only [input_362, List.length_append, input_363_length, input_366_length]

theorem sort_362_correct :
    KernelSort.sortFuel wordLE 15431 input_362 = output_362 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_363 input_366 output_363 output_366 output_362
    input_363_length input_366_length (by decide) (by decide)
    sort_363_correct sort_366_correct (by decide +kernel)

theorem input_370_length : input_370.length = 241 := by
  simp only [input_370, List.length_append, input_371_length, input_374_length]

theorem sort_370_correct :
    KernelSort.sortFuel wordLE 15431 input_370 = output_370 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_371 input_374 output_371 output_374 output_370
    input_371_length input_374_length (by decide) (by decide)
    sort_371_correct sort_374_correct (by decide +kernel)

theorem input_377_length : input_377.length = 242 := by
  simp only [input_377, List.length_append, input_378_length, input_381_length]

theorem sort_377_correct :
    KernelSort.sortFuel wordLE 15431 input_377 = output_377 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_378 input_381 output_378 output_381 output_377
    input_378_length input_381_length (by decide) (by decide)
    sort_378_correct sort_381_correct (by decide +kernel)

theorem input_388_length : input_388.length = 241 := by
  simp only [input_388, List.length_append, input_389_length, input_392_length]

theorem sort_388_correct :
    KernelSort.sortFuel wordLE 15431 input_388 = output_388 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_389 input_392 output_389 output_392 output_388
    input_389_length input_392_length (by decide) (by decide)
    sort_389_correct sort_392_correct (by decide +kernel)

theorem input_395_length : input_395.length = 241 := by
  simp only [input_395, List.length_append, input_396_length, input_399_length]

theorem sort_395_correct :
    KernelSort.sortFuel wordLE 15431 input_395 = output_395 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_396 input_399 output_396 output_399 output_395
    input_396_length input_399_length (by decide) (by decide)
    sort_396_correct sort_399_correct (by decide +kernel)

theorem input_403_length : input_403.length = 241 := by
  simp only [input_403, List.length_append, input_404_length, input_407_length]

theorem sort_403_correct :
    KernelSort.sortFuel wordLE 15431 input_403 = output_403 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_404 input_407 output_404 output_407 output_403
    input_404_length input_407_length (by decide) (by decide)
    sort_404_correct sort_407_correct (by decide +kernel)

theorem input_410_length : input_410.length = 242 := by
  simp only [input_410, List.length_append, input_411_length, input_414_length]

theorem sort_410_correct :
    KernelSort.sortFuel wordLE 15431 input_410 = output_410 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_411 input_414 output_411 output_414 output_410
    input_411_length input_414_length (by decide) (by decide)
    sort_411_correct sort_414_correct (by decide +kernel)

theorem input_419_length : input_419.length = 241 := by
  simp only [input_419, List.length_append, input_420_length, input_423_length]

theorem sort_419_correct :
    KernelSort.sortFuel wordLE 15431 input_419 = output_419 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_420 input_423 output_420 output_423 output_419
    input_420_length input_423_length (by decide) (by decide)
    sort_420_correct sort_423_correct (by decide +kernel)

theorem input_426_length : input_426.length = 241 := by
  simp only [input_426, List.length_append, input_427_length, input_430_length]

theorem sort_426_correct :
    KernelSort.sortFuel wordLE 15431 input_426 = output_426 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_427 input_430 output_427 output_430 output_426
    input_427_length input_430_length (by decide) (by decide)
    sort_427_correct sort_430_correct (by decide +kernel)

theorem input_434_length : input_434.length = 241 := by
  simp only [input_434, List.length_append, input_435_length, input_438_length]

theorem sort_434_correct :
    KernelSort.sortFuel wordLE 15431 input_434 = output_434 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_435 input_438 output_435 output_438 output_434
    input_435_length input_438_length (by decide) (by decide)
    sort_435_correct sort_438_correct (by decide +kernel)

theorem input_441_length : input_441.length = 242 := by
  simp only [input_441, List.length_append, input_442_length, input_445_length]

theorem sort_441_correct :
    KernelSort.sortFuel wordLE 15431 input_441 = output_441 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_442 input_445 output_442 output_445 output_441
    input_442_length input_445_length (by decide) (by decide)
    sort_442_correct sort_445_correct (by decide +kernel)

theorem input_451_length : input_451.length = 241 := by
  simp only [input_451, List.length_append, input_452_length, input_455_length]

theorem sort_451_correct :
    KernelSort.sortFuel wordLE 15431 input_451 = output_451 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_452 input_455 output_452 output_455 output_451
    input_452_length input_455_length (by decide) (by decide)
    sort_452_correct sort_455_correct (by decide +kernel)

theorem input_458_length : input_458.length = 241 := by
  simp only [input_458, List.length_append, input_459_length, input_462_length]

theorem sort_458_correct :
    KernelSort.sortFuel wordLE 15431 input_458 = output_458 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_459 input_462 output_459 output_462 output_458
    input_459_length input_462_length (by decide) (by decide)
    sort_459_correct sort_462_correct (by decide +kernel)

theorem input_466_length : input_466.length = 241 := by
  simp only [input_466, List.length_append, input_467_length, input_470_length]

theorem sort_466_correct :
    KernelSort.sortFuel wordLE 15431 input_466 = output_466 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_467 input_470 output_467 output_470 output_466
    input_467_length input_470_length (by decide) (by decide)
    sort_467_correct sort_470_correct (by decide +kernel)

theorem input_473_length : input_473.length = 242 := by
  simp only [input_473, List.length_append, input_474_length, input_477_length]

theorem sort_473_correct :
    KernelSort.sortFuel wordLE 15431 input_473 = output_473 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_474 input_477 output_474 output_477 output_473
    input_474_length input_477_length (by decide) (by decide)
    sort_474_correct sort_477_correct (by decide +kernel)

theorem input_482_length : input_482.length = 241 := by
  simp only [input_482, List.length_append, input_483_length, input_486_length]

theorem sort_482_correct :
    KernelSort.sortFuel wordLE 15431 input_482 = output_482 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_483 input_486 output_483 output_486 output_482
    input_483_length input_486_length (by decide) (by decide)
    sort_483_correct sort_486_correct (by decide +kernel)

theorem input_489_length : input_489.length = 241 := by
  simp only [input_489, List.length_append, input_490_length, input_493_length]

theorem sort_489_correct :
    KernelSort.sortFuel wordLE 15431 input_489 = output_489 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_490 input_493 output_490 output_493 output_489
    input_490_length input_493_length (by decide) (by decide)
    sort_490_correct sort_493_correct (by decide +kernel)

theorem input_497_length : input_497.length = 241 := by
  simp only [input_497, List.length_append, input_498_length, input_501_length]

theorem sort_497_correct :
    KernelSort.sortFuel wordLE 15431 input_497 = output_497 := by
  exact KernelSort.sortFuel_step wordLE 15430 120 121
    input_498 input_501 output_498 output_501 output_497
    input_498_length input_501_length (by decide) (by decide)
    sort_498_correct sort_501_correct (by decide +kernel)

theorem input_504_length : input_504.length = 242 := by
  simp only [input_504, List.length_append, input_505_length, input_508_length]

theorem sort_504_correct :
    KernelSort.sortFuel wordLE 15431 input_504 = output_504 := by
  exact KernelSort.sortFuel_step wordLE 15430 121 121
    input_505 input_508 output_505 output_508 output_504
    input_505_length input_508_length (by decide) (by decide)
    sort_505_correct sort_508_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
