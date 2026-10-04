module

public import ThomGame.Certificates.LambdaSortData

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_008_length : input_008.length = 60 := by
  decide +kernel

theorem sort_008_correct :
    KernelSort.sortFuel wordLE 15429 input_008 = output_008 := by
  decide +kernel

theorem input_009_length : input_009.length = 60 := by
  decide +kernel

theorem sort_009_correct :
    KernelSort.sortFuel wordLE 15429 input_009 = output_009 := by
  decide +kernel

theorem input_011_length : input_011.length = 60 := by
  decide +kernel

theorem sort_011_correct :
    KernelSort.sortFuel wordLE 15429 input_011 = output_011 := by
  decide +kernel

theorem input_012_length : input_012.length = 61 := by
  decide +kernel

theorem sort_012_correct :
    KernelSort.sortFuel wordLE 15429 input_012 = output_012 := by
  decide +kernel

theorem input_015_length : input_015.length = 60 := by
  decide +kernel

theorem sort_015_correct :
    KernelSort.sortFuel wordLE 15429 input_015 = output_015 := by
  decide +kernel

theorem input_016_length : input_016.length = 60 := by
  decide +kernel

theorem sort_016_correct :
    KernelSort.sortFuel wordLE 15429 input_016 = output_016 := by
  decide +kernel

theorem input_018_length : input_018.length = 60 := by
  decide +kernel

theorem sort_018_correct :
    KernelSort.sortFuel wordLE 15429 input_018 = output_018 := by
  decide +kernel

theorem input_019_length : input_019.length = 61 := by
  decide +kernel

theorem sort_019_correct :
    KernelSort.sortFuel wordLE 15429 input_019 = output_019 := by
  decide +kernel

theorem input_023_length : input_023.length = 60 := by
  decide +kernel

theorem sort_023_correct :
    KernelSort.sortFuel wordLE 15429 input_023 = output_023 := by
  decide +kernel

theorem input_024_length : input_024.length = 60 := by
  decide +kernel

theorem sort_024_correct :
    KernelSort.sortFuel wordLE 15429 input_024 = output_024 := by
  decide +kernel

theorem input_026_length : input_026.length = 60 := by
  decide +kernel

theorem sort_026_correct :
    KernelSort.sortFuel wordLE 15429 input_026 = output_026 := by
  decide +kernel

theorem input_027_length : input_027.length = 61 := by
  decide +kernel

theorem sort_027_correct :
    KernelSort.sortFuel wordLE 15429 input_027 = output_027 := by
  decide +kernel

theorem input_030_length : input_030.length = 60 := by
  decide +kernel

theorem sort_030_correct :
    KernelSort.sortFuel wordLE 15429 input_030 = output_030 := by
  decide +kernel

theorem input_031_length : input_031.length = 60 := by
  decide +kernel

theorem sort_031_correct :
    KernelSort.sortFuel wordLE 15429 input_031 = output_031 := by
  decide +kernel

theorem input_033_length : input_033.length = 60 := by
  decide +kernel

theorem sort_033_correct :
    KernelSort.sortFuel wordLE 15429 input_033 = output_033 := by
  decide +kernel

theorem input_034_length : input_034.length = 61 := by
  decide +kernel

theorem sort_034_correct :
    KernelSort.sortFuel wordLE 15429 input_034 = output_034 := by
  decide +kernel

theorem input_039_length : input_039.length = 60 := by
  decide +kernel

theorem sort_039_correct :
    KernelSort.sortFuel wordLE 15429 input_039 = output_039 := by
  decide +kernel

theorem input_040_length : input_040.length = 60 := by
  decide +kernel

theorem sort_040_correct :
    KernelSort.sortFuel wordLE 15429 input_040 = output_040 := by
  decide +kernel

theorem input_042_length : input_042.length = 60 := by
  decide +kernel

theorem sort_042_correct :
    KernelSort.sortFuel wordLE 15429 input_042 = output_042 := by
  decide +kernel

theorem input_043_length : input_043.length = 61 := by
  decide +kernel

theorem sort_043_correct :
    KernelSort.sortFuel wordLE 15429 input_043 = output_043 := by
  decide +kernel

theorem input_046_length : input_046.length = 60 := by
  decide +kernel

theorem sort_046_correct :
    KernelSort.sortFuel wordLE 15429 input_046 = output_046 := by
  decide +kernel

theorem input_047_length : input_047.length = 60 := by
  decide +kernel

theorem sort_047_correct :
    KernelSort.sortFuel wordLE 15429 input_047 = output_047 := by
  decide +kernel

theorem input_049_length : input_049.length = 60 := by
  decide +kernel

theorem sort_049_correct :
    KernelSort.sortFuel wordLE 15429 input_049 = output_049 := by
  decide +kernel

theorem input_050_length : input_050.length = 61 := by
  decide +kernel

theorem sort_050_correct :
    KernelSort.sortFuel wordLE 15429 input_050 = output_050 := by
  decide +kernel

theorem input_054_length : input_054.length = 60 := by
  decide +kernel

theorem sort_054_correct :
    KernelSort.sortFuel wordLE 15429 input_054 = output_054 := by
  decide +kernel

theorem input_055_length : input_055.length = 60 := by
  decide +kernel

theorem sort_055_correct :
    KernelSort.sortFuel wordLE 15429 input_055 = output_055 := by
  decide +kernel

theorem input_057_length : input_057.length = 60 := by
  decide +kernel

theorem sort_057_correct :
    KernelSort.sortFuel wordLE 15429 input_057 = output_057 := by
  decide +kernel

theorem input_058_length : input_058.length = 61 := by
  decide +kernel

theorem sort_058_correct :
    KernelSort.sortFuel wordLE 15429 input_058 = output_058 := by
  decide +kernel

theorem input_061_length : input_061.length = 60 := by
  decide +kernel

theorem sort_061_correct :
    KernelSort.sortFuel wordLE 15429 input_061 = output_061 := by
  decide +kernel

theorem input_062_length : input_062.length = 61 := by
  decide +kernel

theorem sort_062_correct :
    KernelSort.sortFuel wordLE 15429 input_062 = output_062 := by
  decide +kernel

theorem input_064_length : input_064.length = 60 := by
  decide +kernel

theorem sort_064_correct :
    KernelSort.sortFuel wordLE 15429 input_064 = output_064 := by
  decide +kernel

theorem input_065_length : input_065.length = 61 := by
  decide +kernel

theorem sort_065_correct :
    KernelSort.sortFuel wordLE 15429 input_065 = output_065 := by
  decide +kernel

theorem input_071_length : input_071.length = 60 := by
  decide +kernel

theorem sort_071_correct :
    KernelSort.sortFuel wordLE 15429 input_071 = output_071 := by
  decide +kernel

theorem input_072_length : input_072.length = 60 := by
  decide +kernel

theorem sort_072_correct :
    KernelSort.sortFuel wordLE 15429 input_072 = output_072 := by
  decide +kernel

theorem input_074_length : input_074.length = 60 := by
  decide +kernel

theorem sort_074_correct :
    KernelSort.sortFuel wordLE 15429 input_074 = output_074 := by
  decide +kernel

theorem input_075_length : input_075.length = 61 := by
  decide +kernel

theorem sort_075_correct :
    KernelSort.sortFuel wordLE 15429 input_075 = output_075 := by
  decide +kernel

theorem input_078_length : input_078.length = 60 := by
  decide +kernel

theorem sort_078_correct :
    KernelSort.sortFuel wordLE 15429 input_078 = output_078 := by
  decide +kernel

theorem input_079_length : input_079.length = 60 := by
  decide +kernel

theorem sort_079_correct :
    KernelSort.sortFuel wordLE 15429 input_079 = output_079 := by
  decide +kernel

theorem input_081_length : input_081.length = 60 := by
  decide +kernel

theorem sort_081_correct :
    KernelSort.sortFuel wordLE 15429 input_081 = output_081 := by
  decide +kernel

theorem input_082_length : input_082.length = 61 := by
  decide +kernel

theorem sort_082_correct :
    KernelSort.sortFuel wordLE 15429 input_082 = output_082 := by
  decide +kernel

theorem input_086_length : input_086.length = 60 := by
  decide +kernel

theorem sort_086_correct :
    KernelSort.sortFuel wordLE 15429 input_086 = output_086 := by
  decide +kernel

theorem input_087_length : input_087.length = 60 := by
  decide +kernel

theorem sort_087_correct :
    KernelSort.sortFuel wordLE 15429 input_087 = output_087 := by
  decide +kernel

theorem input_089_length : input_089.length = 60 := by
  decide +kernel

theorem sort_089_correct :
    KernelSort.sortFuel wordLE 15429 input_089 = output_089 := by
  decide +kernel

theorem input_090_length : input_090.length = 61 := by
  decide +kernel

theorem sort_090_correct :
    KernelSort.sortFuel wordLE 15429 input_090 = output_090 := by
  decide +kernel

theorem input_093_length : input_093.length = 60 := by
  decide +kernel

theorem sort_093_correct :
    KernelSort.sortFuel wordLE 15429 input_093 = output_093 := by
  decide +kernel

theorem input_094_length : input_094.length = 61 := by
  decide +kernel

theorem sort_094_correct :
    KernelSort.sortFuel wordLE 15429 input_094 = output_094 := by
  decide +kernel

theorem input_096_length : input_096.length = 60 := by
  decide +kernel

theorem sort_096_correct :
    KernelSort.sortFuel wordLE 15429 input_096 = output_096 := by
  decide +kernel

theorem input_097_length : input_097.length = 61 := by
  decide +kernel

theorem sort_097_correct :
    KernelSort.sortFuel wordLE 15429 input_097 = output_097 := by
  decide +kernel

theorem input_102_length : input_102.length = 60 := by
  decide +kernel

theorem sort_102_correct :
    KernelSort.sortFuel wordLE 15429 input_102 = output_102 := by
  decide +kernel

theorem input_103_length : input_103.length = 60 := by
  decide +kernel

theorem sort_103_correct :
    KernelSort.sortFuel wordLE 15429 input_103 = output_103 := by
  decide +kernel

theorem input_105_length : input_105.length = 60 := by
  decide +kernel

theorem sort_105_correct :
    KernelSort.sortFuel wordLE 15429 input_105 = output_105 := by
  decide +kernel

theorem input_106_length : input_106.length = 61 := by
  decide +kernel

theorem sort_106_correct :
    KernelSort.sortFuel wordLE 15429 input_106 = output_106 := by
  decide +kernel

theorem input_109_length : input_109.length = 60 := by
  decide +kernel

theorem sort_109_correct :
    KernelSort.sortFuel wordLE 15429 input_109 = output_109 := by
  decide +kernel

theorem input_110_length : input_110.length = 60 := by
  decide +kernel

theorem sort_110_correct :
    KernelSort.sortFuel wordLE 15429 input_110 = output_110 := by
  decide +kernel

theorem input_112_length : input_112.length = 60 := by
  decide +kernel

theorem sort_112_correct :
    KernelSort.sortFuel wordLE 15429 input_112 = output_112 := by
  decide +kernel

theorem input_113_length : input_113.length = 61 := by
  decide +kernel

theorem sort_113_correct :
    KernelSort.sortFuel wordLE 15429 input_113 = output_113 := by
  decide +kernel

theorem input_117_length : input_117.length = 60 := by
  decide +kernel

theorem sort_117_correct :
    KernelSort.sortFuel wordLE 15429 input_117 = output_117 := by
  decide +kernel

theorem input_118_length : input_118.length = 60 := by
  decide +kernel

theorem sort_118_correct :
    KernelSort.sortFuel wordLE 15429 input_118 = output_118 := by
  decide +kernel

theorem input_120_length : input_120.length = 60 := by
  decide +kernel

theorem sort_120_correct :
    KernelSort.sortFuel wordLE 15429 input_120 = output_120 := by
  decide +kernel

theorem input_121_length : input_121.length = 61 := by
  decide +kernel

theorem sort_121_correct :
    KernelSort.sortFuel wordLE 15429 input_121 = output_121 := by
  decide +kernel

theorem input_124_length : input_124.length = 60 := by
  decide +kernel

theorem sort_124_correct :
    KernelSort.sortFuel wordLE 15429 input_124 = output_124 := by
  decide +kernel

theorem input_125_length : input_125.length = 61 := by
  decide +kernel

theorem sort_125_correct :
    KernelSort.sortFuel wordLE 15429 input_125 = output_125 := by
  decide +kernel

theorem input_127_length : input_127.length = 60 := by
  decide +kernel

theorem sort_127_correct :
    KernelSort.sortFuel wordLE 15429 input_127 = output_127 := by
  decide +kernel

theorem input_128_length : input_128.length = 61 := by
  decide +kernel

theorem sort_128_correct :
    KernelSort.sortFuel wordLE 15429 input_128 = output_128 := by
  decide +kernel

theorem input_135_length : input_135.length = 60 := by
  decide +kernel

theorem sort_135_correct :
    KernelSort.sortFuel wordLE 15429 input_135 = output_135 := by
  decide +kernel

theorem input_136_length : input_136.length = 60 := by
  decide +kernel

theorem sort_136_correct :
    KernelSort.sortFuel wordLE 15429 input_136 = output_136 := by
  decide +kernel

theorem input_138_length : input_138.length = 60 := by
  decide +kernel

theorem sort_138_correct :
    KernelSort.sortFuel wordLE 15429 input_138 = output_138 := by
  decide +kernel

theorem input_139_length : input_139.length = 61 := by
  decide +kernel

theorem sort_139_correct :
    KernelSort.sortFuel wordLE 15429 input_139 = output_139 := by
  decide +kernel

theorem input_142_length : input_142.length = 60 := by
  decide +kernel

theorem sort_142_correct :
    KernelSort.sortFuel wordLE 15429 input_142 = output_142 := by
  decide +kernel

theorem input_143_length : input_143.length = 60 := by
  decide +kernel

theorem sort_143_correct :
    KernelSort.sortFuel wordLE 15429 input_143 = output_143 := by
  decide +kernel

theorem input_145_length : input_145.length = 60 := by
  decide +kernel

theorem sort_145_correct :
    KernelSort.sortFuel wordLE 15429 input_145 = output_145 := by
  decide +kernel

theorem input_146_length : input_146.length = 61 := by
  decide +kernel

theorem sort_146_correct :
    KernelSort.sortFuel wordLE 15429 input_146 = output_146 := by
  decide +kernel

theorem input_150_length : input_150.length = 60 := by
  decide +kernel

theorem sort_150_correct :
    KernelSort.sortFuel wordLE 15429 input_150 = output_150 := by
  decide +kernel

theorem input_151_length : input_151.length = 60 := by
  decide +kernel

theorem sort_151_correct :
    KernelSort.sortFuel wordLE 15429 input_151 = output_151 := by
  decide +kernel

theorem input_153_length : input_153.length = 60 := by
  decide +kernel

theorem sort_153_correct :
    KernelSort.sortFuel wordLE 15429 input_153 = output_153 := by
  decide +kernel

theorem input_154_length : input_154.length = 61 := by
  decide +kernel

theorem sort_154_correct :
    KernelSort.sortFuel wordLE 15429 input_154 = output_154 := by
  decide +kernel

theorem input_157_length : input_157.length = 60 := by
  decide +kernel

theorem sort_157_correct :
    KernelSort.sortFuel wordLE 15429 input_157 = output_157 := by
  decide +kernel

theorem input_158_length : input_158.length = 60 := by
  decide +kernel

theorem sort_158_correct :
    KernelSort.sortFuel wordLE 15429 input_158 = output_158 := by
  decide +kernel

theorem input_160_length : input_160.length = 60 := by
  decide +kernel

theorem sort_160_correct :
    KernelSort.sortFuel wordLE 15429 input_160 = output_160 := by
  decide +kernel

theorem input_161_length : input_161.length = 61 := by
  decide +kernel

theorem sort_161_correct :
    KernelSort.sortFuel wordLE 15429 input_161 = output_161 := by
  decide +kernel

theorem input_166_length : input_166.length = 60 := by
  decide +kernel

theorem sort_166_correct :
    KernelSort.sortFuel wordLE 15429 input_166 = output_166 := by
  decide +kernel

theorem input_167_length : input_167.length = 60 := by
  decide +kernel

theorem sort_167_correct :
    KernelSort.sortFuel wordLE 15429 input_167 = output_167 := by
  decide +kernel

theorem input_169_length : input_169.length = 60 := by
  decide +kernel

theorem sort_169_correct :
    KernelSort.sortFuel wordLE 15429 input_169 = output_169 := by
  decide +kernel

theorem input_170_length : input_170.length = 61 := by
  decide +kernel

theorem sort_170_correct :
    KernelSort.sortFuel wordLE 15429 input_170 = output_170 := by
  decide +kernel

theorem input_173_length : input_173.length = 60 := by
  decide +kernel

theorem sort_173_correct :
    KernelSort.sortFuel wordLE 15429 input_173 = output_173 := by
  decide +kernel

theorem input_174_length : input_174.length = 60 := by
  decide +kernel

theorem sort_174_correct :
    KernelSort.sortFuel wordLE 15429 input_174 = output_174 := by
  decide +kernel

theorem input_176_length : input_176.length = 60 := by
  decide +kernel

theorem sort_176_correct :
    KernelSort.sortFuel wordLE 15429 input_176 = output_176 := by
  decide +kernel

theorem input_177_length : input_177.length = 61 := by
  decide +kernel

theorem sort_177_correct :
    KernelSort.sortFuel wordLE 15429 input_177 = output_177 := by
  decide +kernel

theorem input_181_length : input_181.length = 60 := by
  decide +kernel

theorem sort_181_correct :
    KernelSort.sortFuel wordLE 15429 input_181 = output_181 := by
  decide +kernel

theorem input_182_length : input_182.length = 60 := by
  decide +kernel

theorem sort_182_correct :
    KernelSort.sortFuel wordLE 15429 input_182 = output_182 := by
  decide +kernel

theorem input_184_length : input_184.length = 60 := by
  decide +kernel

theorem sort_184_correct :
    KernelSort.sortFuel wordLE 15429 input_184 = output_184 := by
  decide +kernel

theorem input_185_length : input_185.length = 61 := by
  decide +kernel

theorem sort_185_correct :
    KernelSort.sortFuel wordLE 15429 input_185 = output_185 := by
  decide +kernel

theorem input_188_length : input_188.length = 60 := by
  decide +kernel

theorem sort_188_correct :
    KernelSort.sortFuel wordLE 15429 input_188 = output_188 := by
  decide +kernel

theorem input_189_length : input_189.length = 61 := by
  decide +kernel

theorem sort_189_correct :
    KernelSort.sortFuel wordLE 15429 input_189 = output_189 := by
  decide +kernel

theorem input_191_length : input_191.length = 60 := by
  decide +kernel

theorem sort_191_correct :
    KernelSort.sortFuel wordLE 15429 input_191 = output_191 := by
  decide +kernel

theorem input_192_length : input_192.length = 61 := by
  decide +kernel

theorem sort_192_correct :
    KernelSort.sortFuel wordLE 15429 input_192 = output_192 := by
  decide +kernel

theorem input_198_length : input_198.length = 60 := by
  decide +kernel

theorem sort_198_correct :
    KernelSort.sortFuel wordLE 15429 input_198 = output_198 := by
  decide +kernel

theorem input_199_length : input_199.length = 60 := by
  decide +kernel

theorem sort_199_correct :
    KernelSort.sortFuel wordLE 15429 input_199 = output_199 := by
  decide +kernel

theorem input_201_length : input_201.length = 60 := by
  decide +kernel

theorem sort_201_correct :
    KernelSort.sortFuel wordLE 15429 input_201 = output_201 := by
  decide +kernel

theorem input_202_length : input_202.length = 61 := by
  decide +kernel

theorem sort_202_correct :
    KernelSort.sortFuel wordLE 15429 input_202 = output_202 := by
  decide +kernel

theorem input_205_length : input_205.length = 60 := by
  decide +kernel

theorem sort_205_correct :
    KernelSort.sortFuel wordLE 15429 input_205 = output_205 := by
  decide +kernel

theorem input_206_length : input_206.length = 60 := by
  decide +kernel

theorem sort_206_correct :
    KernelSort.sortFuel wordLE 15429 input_206 = output_206 := by
  decide +kernel

theorem input_208_length : input_208.length = 60 := by
  decide +kernel

theorem sort_208_correct :
    KernelSort.sortFuel wordLE 15429 input_208 = output_208 := by
  decide +kernel

theorem input_209_length : input_209.length = 61 := by
  decide +kernel

theorem sort_209_correct :
    KernelSort.sortFuel wordLE 15429 input_209 = output_209 := by
  decide +kernel

theorem input_213_length : input_213.length = 60 := by
  decide +kernel

theorem sort_213_correct :
    KernelSort.sortFuel wordLE 15429 input_213 = output_213 := by
  decide +kernel

theorem input_214_length : input_214.length = 60 := by
  decide +kernel

theorem sort_214_correct :
    KernelSort.sortFuel wordLE 15429 input_214 = output_214 := by
  decide +kernel

theorem input_216_length : input_216.length = 60 := by
  decide +kernel

theorem sort_216_correct :
    KernelSort.sortFuel wordLE 15429 input_216 = output_216 := by
  decide +kernel

theorem input_217_length : input_217.length = 61 := by
  decide +kernel

theorem sort_217_correct :
    KernelSort.sortFuel wordLE 15429 input_217 = output_217 := by
  decide +kernel

theorem input_220_length : input_220.length = 60 := by
  decide +kernel

theorem sort_220_correct :
    KernelSort.sortFuel wordLE 15429 input_220 = output_220 := by
  decide +kernel

theorem input_221_length : input_221.length = 61 := by
  decide +kernel

theorem sort_221_correct :
    KernelSort.sortFuel wordLE 15429 input_221 = output_221 := by
  decide +kernel

theorem input_223_length : input_223.length = 60 := by
  decide +kernel

theorem sort_223_correct :
    KernelSort.sortFuel wordLE 15429 input_223 = output_223 := by
  decide +kernel

theorem input_224_length : input_224.length = 61 := by
  decide +kernel

theorem sort_224_correct :
    KernelSort.sortFuel wordLE 15429 input_224 = output_224 := by
  decide +kernel

theorem input_229_length : input_229.length = 60 := by
  decide +kernel

theorem sort_229_correct :
    KernelSort.sortFuel wordLE 15429 input_229 = output_229 := by
  decide +kernel

theorem input_230_length : input_230.length = 60 := by
  decide +kernel

theorem sort_230_correct :
    KernelSort.sortFuel wordLE 15429 input_230 = output_230 := by
  decide +kernel

theorem input_232_length : input_232.length = 60 := by
  decide +kernel

theorem sort_232_correct :
    KernelSort.sortFuel wordLE 15429 input_232 = output_232 := by
  decide +kernel

theorem input_233_length : input_233.length = 61 := by
  decide +kernel

theorem sort_233_correct :
    KernelSort.sortFuel wordLE 15429 input_233 = output_233 := by
  decide +kernel

theorem input_236_length : input_236.length = 60 := by
  decide +kernel

theorem sort_236_correct :
    KernelSort.sortFuel wordLE 15429 input_236 = output_236 := by
  decide +kernel

theorem input_237_length : input_237.length = 60 := by
  decide +kernel

theorem sort_237_correct :
    KernelSort.sortFuel wordLE 15429 input_237 = output_237 := by
  decide +kernel

theorem input_239_length : input_239.length = 60 := by
  decide +kernel

theorem sort_239_correct :
    KernelSort.sortFuel wordLE 15429 input_239 = output_239 := by
  decide +kernel

theorem input_240_length : input_240.length = 61 := by
  decide +kernel

theorem sort_240_correct :
    KernelSort.sortFuel wordLE 15429 input_240 = output_240 := by
  decide +kernel

theorem input_244_length : input_244.length = 60 := by
  decide +kernel

theorem sort_244_correct :
    KernelSort.sortFuel wordLE 15429 input_244 = output_244 := by
  decide +kernel

theorem input_245_length : input_245.length = 60 := by
  decide +kernel

theorem sort_245_correct :
    KernelSort.sortFuel wordLE 15429 input_245 = output_245 := by
  decide +kernel

theorem input_247_length : input_247.length = 60 := by
  decide +kernel

theorem sort_247_correct :
    KernelSort.sortFuel wordLE 15429 input_247 = output_247 := by
  decide +kernel

theorem input_248_length : input_248.length = 61 := by
  decide +kernel

theorem sort_248_correct :
    KernelSort.sortFuel wordLE 15429 input_248 = output_248 := by
  decide +kernel

theorem input_251_length : input_251.length = 60 := by
  decide +kernel

theorem sort_251_correct :
    KernelSort.sortFuel wordLE 15429 input_251 = output_251 := by
  decide +kernel

theorem input_252_length : input_252.length = 61 := by
  decide +kernel

theorem sort_252_correct :
    KernelSort.sortFuel wordLE 15429 input_252 = output_252 := by
  decide +kernel

theorem input_254_length : input_254.length = 60 := by
  decide +kernel

theorem sort_254_correct :
    KernelSort.sortFuel wordLE 15429 input_254 = output_254 := by
  decide +kernel

theorem input_255_length : input_255.length = 61 := by
  decide +kernel

theorem sort_255_correct :
    KernelSort.sortFuel wordLE 15429 input_255 = output_255 := by
  decide +kernel

theorem input_263_length : input_263.length = 60 := by
  decide +kernel

theorem sort_263_correct :
    KernelSort.sortFuel wordLE 15429 input_263 = output_263 := by
  decide +kernel

theorem input_264_length : input_264.length = 60 := by
  decide +kernel

theorem sort_264_correct :
    KernelSort.sortFuel wordLE 15429 input_264 = output_264 := by
  decide +kernel

theorem input_266_length : input_266.length = 60 := by
  decide +kernel

theorem sort_266_correct :
    KernelSort.sortFuel wordLE 15429 input_266 = output_266 := by
  decide +kernel

theorem input_267_length : input_267.length = 61 := by
  decide +kernel

theorem sort_267_correct :
    KernelSort.sortFuel wordLE 15429 input_267 = output_267 := by
  decide +kernel

theorem input_270_length : input_270.length = 60 := by
  decide +kernel

theorem sort_270_correct :
    KernelSort.sortFuel wordLE 15429 input_270 = output_270 := by
  decide +kernel

theorem input_271_length : input_271.length = 60 := by
  decide +kernel

theorem sort_271_correct :
    KernelSort.sortFuel wordLE 15429 input_271 = output_271 := by
  decide +kernel

theorem input_273_length : input_273.length = 60 := by
  decide +kernel

theorem sort_273_correct :
    KernelSort.sortFuel wordLE 15429 input_273 = output_273 := by
  decide +kernel

theorem input_274_length : input_274.length = 61 := by
  decide +kernel

theorem sort_274_correct :
    KernelSort.sortFuel wordLE 15429 input_274 = output_274 := by
  decide +kernel

theorem input_278_length : input_278.length = 60 := by
  decide +kernel

theorem sort_278_correct :
    KernelSort.sortFuel wordLE 15429 input_278 = output_278 := by
  decide +kernel

theorem input_279_length : input_279.length = 60 := by
  decide +kernel

theorem sort_279_correct :
    KernelSort.sortFuel wordLE 15429 input_279 = output_279 := by
  decide +kernel

theorem input_281_length : input_281.length = 60 := by
  decide +kernel

theorem sort_281_correct :
    KernelSort.sortFuel wordLE 15429 input_281 = output_281 := by
  decide +kernel

theorem input_282_length : input_282.length = 61 := by
  decide +kernel

theorem sort_282_correct :
    KernelSort.sortFuel wordLE 15429 input_282 = output_282 := by
  decide +kernel

theorem input_285_length : input_285.length = 60 := by
  decide +kernel

theorem sort_285_correct :
    KernelSort.sortFuel wordLE 15429 input_285 = output_285 := by
  decide +kernel

theorem input_286_length : input_286.length = 60 := by
  decide +kernel

theorem sort_286_correct :
    KernelSort.sortFuel wordLE 15429 input_286 = output_286 := by
  decide +kernel

theorem input_288_length : input_288.length = 60 := by
  decide +kernel

theorem sort_288_correct :
    KernelSort.sortFuel wordLE 15429 input_288 = output_288 := by
  decide +kernel

theorem input_289_length : input_289.length = 61 := by
  decide +kernel

theorem sort_289_correct :
    KernelSort.sortFuel wordLE 15429 input_289 = output_289 := by
  decide +kernel

theorem input_294_length : input_294.length = 60 := by
  decide +kernel

theorem sort_294_correct :
    KernelSort.sortFuel wordLE 15429 input_294 = output_294 := by
  decide +kernel

theorem input_295_length : input_295.length = 60 := by
  decide +kernel

theorem sort_295_correct :
    KernelSort.sortFuel wordLE 15429 input_295 = output_295 := by
  decide +kernel

theorem input_297_length : input_297.length = 60 := by
  decide +kernel

theorem sort_297_correct :
    KernelSort.sortFuel wordLE 15429 input_297 = output_297 := by
  decide +kernel

theorem input_298_length : input_298.length = 61 := by
  decide +kernel

theorem sort_298_correct :
    KernelSort.sortFuel wordLE 15429 input_298 = output_298 := by
  decide +kernel

theorem input_301_length : input_301.length = 60 := by
  decide +kernel

theorem sort_301_correct :
    KernelSort.sortFuel wordLE 15429 input_301 = output_301 := by
  decide +kernel

theorem input_302_length : input_302.length = 60 := by
  decide +kernel

theorem sort_302_correct :
    KernelSort.sortFuel wordLE 15429 input_302 = output_302 := by
  decide +kernel

theorem input_304_length : input_304.length = 60 := by
  decide +kernel

theorem sort_304_correct :
    KernelSort.sortFuel wordLE 15429 input_304 = output_304 := by
  decide +kernel

theorem input_305_length : input_305.length = 61 := by
  decide +kernel

theorem sort_305_correct :
    KernelSort.sortFuel wordLE 15429 input_305 = output_305 := by
  decide +kernel

theorem input_309_length : input_309.length = 60 := by
  decide +kernel

theorem sort_309_correct :
    KernelSort.sortFuel wordLE 15429 input_309 = output_309 := by
  decide +kernel

theorem input_310_length : input_310.length = 60 := by
  decide +kernel

theorem sort_310_correct :
    KernelSort.sortFuel wordLE 15429 input_310 = output_310 := by
  decide +kernel

theorem input_312_length : input_312.length = 60 := by
  decide +kernel

theorem sort_312_correct :
    KernelSort.sortFuel wordLE 15429 input_312 = output_312 := by
  decide +kernel

theorem input_313_length : input_313.length = 61 := by
  decide +kernel

theorem sort_313_correct :
    KernelSort.sortFuel wordLE 15429 input_313 = output_313 := by
  decide +kernel

theorem input_316_length : input_316.length = 60 := by
  decide +kernel

theorem sort_316_correct :
    KernelSort.sortFuel wordLE 15429 input_316 = output_316 := by
  decide +kernel

theorem input_317_length : input_317.length = 61 := by
  decide +kernel

theorem sort_317_correct :
    KernelSort.sortFuel wordLE 15429 input_317 = output_317 := by
  decide +kernel

theorem input_319_length : input_319.length = 60 := by
  decide +kernel

theorem sort_319_correct :
    KernelSort.sortFuel wordLE 15429 input_319 = output_319 := by
  decide +kernel

theorem input_320_length : input_320.length = 61 := by
  decide +kernel

theorem sort_320_correct :
    KernelSort.sortFuel wordLE 15429 input_320 = output_320 := by
  decide +kernel

theorem input_326_length : input_326.length = 60 := by
  decide +kernel

theorem sort_326_correct :
    KernelSort.sortFuel wordLE 15429 input_326 = output_326 := by
  decide +kernel

theorem input_327_length : input_327.length = 60 := by
  decide +kernel

theorem sort_327_correct :
    KernelSort.sortFuel wordLE 15429 input_327 = output_327 := by
  decide +kernel

theorem input_329_length : input_329.length = 60 := by
  decide +kernel

theorem sort_329_correct :
    KernelSort.sortFuel wordLE 15429 input_329 = output_329 := by
  decide +kernel

theorem input_330_length : input_330.length = 61 := by
  decide +kernel

theorem sort_330_correct :
    KernelSort.sortFuel wordLE 15429 input_330 = output_330 := by
  decide +kernel

theorem input_333_length : input_333.length = 60 := by
  decide +kernel

theorem sort_333_correct :
    KernelSort.sortFuel wordLE 15429 input_333 = output_333 := by
  decide +kernel

theorem input_334_length : input_334.length = 60 := by
  decide +kernel

theorem sort_334_correct :
    KernelSort.sortFuel wordLE 15429 input_334 = output_334 := by
  decide +kernel

theorem input_336_length : input_336.length = 60 := by
  decide +kernel

theorem sort_336_correct :
    KernelSort.sortFuel wordLE 15429 input_336 = output_336 := by
  decide +kernel

theorem input_337_length : input_337.length = 61 := by
  decide +kernel

theorem sort_337_correct :
    KernelSort.sortFuel wordLE 15429 input_337 = output_337 := by
  decide +kernel

theorem input_341_length : input_341.length = 60 := by
  decide +kernel

theorem sort_341_correct :
    KernelSort.sortFuel wordLE 15429 input_341 = output_341 := by
  decide +kernel

theorem input_342_length : input_342.length = 60 := by
  decide +kernel

theorem sort_342_correct :
    KernelSort.sortFuel wordLE 15429 input_342 = output_342 := by
  decide +kernel

theorem input_344_length : input_344.length = 60 := by
  decide +kernel

theorem sort_344_correct :
    KernelSort.sortFuel wordLE 15429 input_344 = output_344 := by
  decide +kernel

theorem input_345_length : input_345.length = 61 := by
  decide +kernel

theorem sort_345_correct :
    KernelSort.sortFuel wordLE 15429 input_345 = output_345 := by
  decide +kernel

theorem input_348_length : input_348.length = 60 := by
  decide +kernel

theorem sort_348_correct :
    KernelSort.sortFuel wordLE 15429 input_348 = output_348 := by
  decide +kernel

theorem input_349_length : input_349.length = 61 := by
  decide +kernel

theorem sort_349_correct :
    KernelSort.sortFuel wordLE 15429 input_349 = output_349 := by
  decide +kernel

theorem input_351_length : input_351.length = 60 := by
  decide +kernel

theorem sort_351_correct :
    KernelSort.sortFuel wordLE 15429 input_351 = output_351 := by
  decide +kernel

theorem input_352_length : input_352.length = 61 := by
  decide +kernel

theorem sort_352_correct :
    KernelSort.sortFuel wordLE 15429 input_352 = output_352 := by
  decide +kernel

theorem input_357_length : input_357.length = 60 := by
  decide +kernel

theorem sort_357_correct :
    KernelSort.sortFuel wordLE 15429 input_357 = output_357 := by
  decide +kernel

theorem input_358_length : input_358.length = 60 := by
  decide +kernel

theorem sort_358_correct :
    KernelSort.sortFuel wordLE 15429 input_358 = output_358 := by
  decide +kernel

theorem input_360_length : input_360.length = 60 := by
  decide +kernel

theorem sort_360_correct :
    KernelSort.sortFuel wordLE 15429 input_360 = output_360 := by
  decide +kernel

theorem input_361_length : input_361.length = 61 := by
  decide +kernel

theorem sort_361_correct :
    KernelSort.sortFuel wordLE 15429 input_361 = output_361 := by
  decide +kernel

theorem input_364_length : input_364.length = 60 := by
  decide +kernel

theorem sort_364_correct :
    KernelSort.sortFuel wordLE 15429 input_364 = output_364 := by
  decide +kernel

theorem input_365_length : input_365.length = 60 := by
  decide +kernel

theorem sort_365_correct :
    KernelSort.sortFuel wordLE 15429 input_365 = output_365 := by
  decide +kernel

theorem input_367_length : input_367.length = 60 := by
  decide +kernel

theorem sort_367_correct :
    KernelSort.sortFuel wordLE 15429 input_367 = output_367 := by
  decide +kernel

theorem input_368_length : input_368.length = 61 := by
  decide +kernel

theorem sort_368_correct :
    KernelSort.sortFuel wordLE 15429 input_368 = output_368 := by
  decide +kernel

theorem input_372_length : input_372.length = 60 := by
  decide +kernel

theorem sort_372_correct :
    KernelSort.sortFuel wordLE 15429 input_372 = output_372 := by
  decide +kernel

theorem input_373_length : input_373.length = 60 := by
  decide +kernel

theorem sort_373_correct :
    KernelSort.sortFuel wordLE 15429 input_373 = output_373 := by
  decide +kernel

theorem input_375_length : input_375.length = 60 := by
  decide +kernel

theorem sort_375_correct :
    KernelSort.sortFuel wordLE 15429 input_375 = output_375 := by
  decide +kernel

theorem input_376_length : input_376.length = 61 := by
  decide +kernel

theorem sort_376_correct :
    KernelSort.sortFuel wordLE 15429 input_376 = output_376 := by
  decide +kernel

theorem input_379_length : input_379.length = 60 := by
  decide +kernel

theorem sort_379_correct :
    KernelSort.sortFuel wordLE 15429 input_379 = output_379 := by
  decide +kernel

theorem input_380_length : input_380.length = 61 := by
  decide +kernel

theorem sort_380_correct :
    KernelSort.sortFuel wordLE 15429 input_380 = output_380 := by
  decide +kernel

theorem input_382_length : input_382.length = 60 := by
  decide +kernel

theorem sort_382_correct :
    KernelSort.sortFuel wordLE 15429 input_382 = output_382 := by
  decide +kernel

theorem input_383_length : input_383.length = 61 := by
  decide +kernel

theorem sort_383_correct :
    KernelSort.sortFuel wordLE 15429 input_383 = output_383 := by
  decide +kernel

theorem input_390_length : input_390.length = 60 := by
  decide +kernel

theorem sort_390_correct :
    KernelSort.sortFuel wordLE 15429 input_390 = output_390 := by
  decide +kernel

theorem input_391_length : input_391.length = 60 := by
  decide +kernel

theorem sort_391_correct :
    KernelSort.sortFuel wordLE 15429 input_391 = output_391 := by
  decide +kernel

theorem input_393_length : input_393.length = 60 := by
  decide +kernel

theorem sort_393_correct :
    KernelSort.sortFuel wordLE 15429 input_393 = output_393 := by
  decide +kernel

theorem input_394_length : input_394.length = 61 := by
  decide +kernel

theorem sort_394_correct :
    KernelSort.sortFuel wordLE 15429 input_394 = output_394 := by
  decide +kernel

theorem input_397_length : input_397.length = 60 := by
  decide +kernel

theorem sort_397_correct :
    KernelSort.sortFuel wordLE 15429 input_397 = output_397 := by
  decide +kernel

theorem input_398_length : input_398.length = 60 := by
  decide +kernel

theorem sort_398_correct :
    KernelSort.sortFuel wordLE 15429 input_398 = output_398 := by
  decide +kernel

theorem input_400_length : input_400.length = 60 := by
  decide +kernel

theorem sort_400_correct :
    KernelSort.sortFuel wordLE 15429 input_400 = output_400 := by
  decide +kernel

theorem input_401_length : input_401.length = 61 := by
  decide +kernel

theorem sort_401_correct :
    KernelSort.sortFuel wordLE 15429 input_401 = output_401 := by
  decide +kernel

theorem input_405_length : input_405.length = 60 := by
  decide +kernel

theorem sort_405_correct :
    KernelSort.sortFuel wordLE 15429 input_405 = output_405 := by
  decide +kernel

theorem input_406_length : input_406.length = 60 := by
  decide +kernel

theorem sort_406_correct :
    KernelSort.sortFuel wordLE 15429 input_406 = output_406 := by
  decide +kernel

theorem input_408_length : input_408.length = 60 := by
  decide +kernel

theorem sort_408_correct :
    KernelSort.sortFuel wordLE 15429 input_408 = output_408 := by
  decide +kernel

theorem input_409_length : input_409.length = 61 := by
  decide +kernel

theorem sort_409_correct :
    KernelSort.sortFuel wordLE 15429 input_409 = output_409 := by
  decide +kernel

theorem input_412_length : input_412.length = 60 := by
  decide +kernel

theorem sort_412_correct :
    KernelSort.sortFuel wordLE 15429 input_412 = output_412 := by
  decide +kernel

theorem input_413_length : input_413.length = 61 := by
  decide +kernel

theorem sort_413_correct :
    KernelSort.sortFuel wordLE 15429 input_413 = output_413 := by
  decide +kernel

theorem input_415_length : input_415.length = 60 := by
  decide +kernel

theorem sort_415_correct :
    KernelSort.sortFuel wordLE 15429 input_415 = output_415 := by
  decide +kernel

theorem input_416_length : input_416.length = 61 := by
  decide +kernel

theorem sort_416_correct :
    KernelSort.sortFuel wordLE 15429 input_416 = output_416 := by
  decide +kernel

theorem input_421_length : input_421.length = 60 := by
  decide +kernel

theorem sort_421_correct :
    KernelSort.sortFuel wordLE 15429 input_421 = output_421 := by
  decide +kernel

theorem input_422_length : input_422.length = 60 := by
  decide +kernel

theorem sort_422_correct :
    KernelSort.sortFuel wordLE 15429 input_422 = output_422 := by
  decide +kernel

theorem input_424_length : input_424.length = 60 := by
  decide +kernel

theorem sort_424_correct :
    KernelSort.sortFuel wordLE 15429 input_424 = output_424 := by
  decide +kernel

theorem input_425_length : input_425.length = 61 := by
  decide +kernel

theorem sort_425_correct :
    KernelSort.sortFuel wordLE 15429 input_425 = output_425 := by
  decide +kernel

theorem input_428_length : input_428.length = 60 := by
  decide +kernel

theorem sort_428_correct :
    KernelSort.sortFuel wordLE 15429 input_428 = output_428 := by
  decide +kernel

theorem input_429_length : input_429.length = 60 := by
  decide +kernel

theorem sort_429_correct :
    KernelSort.sortFuel wordLE 15429 input_429 = output_429 := by
  decide +kernel

theorem input_431_length : input_431.length = 60 := by
  decide +kernel

theorem sort_431_correct :
    KernelSort.sortFuel wordLE 15429 input_431 = output_431 := by
  decide +kernel

theorem input_432_length : input_432.length = 61 := by
  decide +kernel

theorem sort_432_correct :
    KernelSort.sortFuel wordLE 15429 input_432 = output_432 := by
  decide +kernel

theorem input_436_length : input_436.length = 60 := by
  decide +kernel

theorem sort_436_correct :
    KernelSort.sortFuel wordLE 15429 input_436 = output_436 := by
  decide +kernel

theorem input_437_length : input_437.length = 60 := by
  decide +kernel

theorem sort_437_correct :
    KernelSort.sortFuel wordLE 15429 input_437 = output_437 := by
  decide +kernel

theorem input_439_length : input_439.length = 60 := by
  decide +kernel

theorem sort_439_correct :
    KernelSort.sortFuel wordLE 15429 input_439 = output_439 := by
  decide +kernel

theorem input_440_length : input_440.length = 61 := by
  decide +kernel

theorem sort_440_correct :
    KernelSort.sortFuel wordLE 15429 input_440 = output_440 := by
  decide +kernel

theorem input_443_length : input_443.length = 60 := by
  decide +kernel

theorem sort_443_correct :
    KernelSort.sortFuel wordLE 15429 input_443 = output_443 := by
  decide +kernel

theorem input_444_length : input_444.length = 61 := by
  decide +kernel

theorem sort_444_correct :
    KernelSort.sortFuel wordLE 15429 input_444 = output_444 := by
  decide +kernel

theorem input_446_length : input_446.length = 60 := by
  decide +kernel

theorem sort_446_correct :
    KernelSort.sortFuel wordLE 15429 input_446 = output_446 := by
  decide +kernel

theorem input_447_length : input_447.length = 61 := by
  decide +kernel

theorem sort_447_correct :
    KernelSort.sortFuel wordLE 15429 input_447 = output_447 := by
  decide +kernel

theorem input_453_length : input_453.length = 60 := by
  decide +kernel

theorem sort_453_correct :
    KernelSort.sortFuel wordLE 15429 input_453 = output_453 := by
  decide +kernel

theorem input_454_length : input_454.length = 60 := by
  decide +kernel

theorem sort_454_correct :
    KernelSort.sortFuel wordLE 15429 input_454 = output_454 := by
  decide +kernel

theorem input_456_length : input_456.length = 60 := by
  decide +kernel

theorem sort_456_correct :
    KernelSort.sortFuel wordLE 15429 input_456 = output_456 := by
  decide +kernel

theorem input_457_length : input_457.length = 61 := by
  decide +kernel

theorem sort_457_correct :
    KernelSort.sortFuel wordLE 15429 input_457 = output_457 := by
  decide +kernel

theorem input_460_length : input_460.length = 60 := by
  decide +kernel

theorem sort_460_correct :
    KernelSort.sortFuel wordLE 15429 input_460 = output_460 := by
  decide +kernel

theorem input_461_length : input_461.length = 60 := by
  decide +kernel

theorem sort_461_correct :
    KernelSort.sortFuel wordLE 15429 input_461 = output_461 := by
  decide +kernel

theorem input_463_length : input_463.length = 60 := by
  decide +kernel

theorem sort_463_correct :
    KernelSort.sortFuel wordLE 15429 input_463 = output_463 := by
  decide +kernel

theorem input_464_length : input_464.length = 61 := by
  decide +kernel

theorem sort_464_correct :
    KernelSort.sortFuel wordLE 15429 input_464 = output_464 := by
  decide +kernel

theorem input_468_length : input_468.length = 60 := by
  decide +kernel

theorem sort_468_correct :
    KernelSort.sortFuel wordLE 15429 input_468 = output_468 := by
  decide +kernel

theorem input_469_length : input_469.length = 60 := by
  decide +kernel

theorem sort_469_correct :
    KernelSort.sortFuel wordLE 15429 input_469 = output_469 := by
  decide +kernel

theorem input_471_length : input_471.length = 60 := by
  decide +kernel

theorem sort_471_correct :
    KernelSort.sortFuel wordLE 15429 input_471 = output_471 := by
  decide +kernel

theorem input_472_length : input_472.length = 61 := by
  decide +kernel

theorem sort_472_correct :
    KernelSort.sortFuel wordLE 15429 input_472 = output_472 := by
  decide +kernel

theorem input_475_length : input_475.length = 60 := by
  decide +kernel

theorem sort_475_correct :
    KernelSort.sortFuel wordLE 15429 input_475 = output_475 := by
  decide +kernel

theorem input_476_length : input_476.length = 61 := by
  decide +kernel

theorem sort_476_correct :
    KernelSort.sortFuel wordLE 15429 input_476 = output_476 := by
  decide +kernel

theorem input_478_length : input_478.length = 60 := by
  decide +kernel

theorem sort_478_correct :
    KernelSort.sortFuel wordLE 15429 input_478 = output_478 := by
  decide +kernel

theorem input_479_length : input_479.length = 61 := by
  decide +kernel

theorem sort_479_correct :
    KernelSort.sortFuel wordLE 15429 input_479 = output_479 := by
  decide +kernel

theorem input_484_length : input_484.length = 60 := by
  decide +kernel

theorem sort_484_correct :
    KernelSort.sortFuel wordLE 15429 input_484 = output_484 := by
  decide +kernel

theorem input_485_length : input_485.length = 60 := by
  decide +kernel

theorem sort_485_correct :
    KernelSort.sortFuel wordLE 15429 input_485 = output_485 := by
  decide +kernel

theorem input_487_length : input_487.length = 60 := by
  decide +kernel

theorem sort_487_correct :
    KernelSort.sortFuel wordLE 15429 input_487 = output_487 := by
  decide +kernel

theorem input_488_length : input_488.length = 61 := by
  decide +kernel

theorem sort_488_correct :
    KernelSort.sortFuel wordLE 15429 input_488 = output_488 := by
  decide +kernel

theorem input_491_length : input_491.length = 60 := by
  decide +kernel

theorem sort_491_correct :
    KernelSort.sortFuel wordLE 15429 input_491 = output_491 := by
  decide +kernel

theorem input_492_length : input_492.length = 60 := by
  decide +kernel

theorem sort_492_correct :
    KernelSort.sortFuel wordLE 15429 input_492 = output_492 := by
  decide +kernel

theorem input_494_length : input_494.length = 60 := by
  decide +kernel

theorem sort_494_correct :
    KernelSort.sortFuel wordLE 15429 input_494 = output_494 := by
  decide +kernel

theorem input_495_length : input_495.length = 61 := by
  decide +kernel

theorem sort_495_correct :
    KernelSort.sortFuel wordLE 15429 input_495 = output_495 := by
  decide +kernel

theorem input_499_length : input_499.length = 60 := by
  decide +kernel

theorem sort_499_correct :
    KernelSort.sortFuel wordLE 15429 input_499 = output_499 := by
  decide +kernel

theorem input_500_length : input_500.length = 60 := by
  decide +kernel

theorem sort_500_correct :
    KernelSort.sortFuel wordLE 15429 input_500 = output_500 := by
  decide +kernel

theorem input_502_length : input_502.length = 60 := by
  decide +kernel

theorem sort_502_correct :
    KernelSort.sortFuel wordLE 15429 input_502 = output_502 := by
  decide +kernel

theorem input_503_length : input_503.length = 61 := by
  decide +kernel

theorem sort_503_correct :
    KernelSort.sortFuel wordLE 15429 input_503 = output_503 := by
  decide +kernel

theorem input_506_length : input_506.length = 60 := by
  decide +kernel

theorem sort_506_correct :
    KernelSort.sortFuel wordLE 15429 input_506 = output_506 := by
  decide +kernel

theorem input_507_length : input_507.length = 61 := by
  decide +kernel

theorem sort_507_correct :
    KernelSort.sortFuel wordLE 15429 input_507 = output_507 := by
  decide +kernel

theorem input_509_length : input_509.length = 60 := by
  decide +kernel

theorem sort_509_correct :
    KernelSort.sortFuel wordLE 15429 input_509 = output_509 := by
  decide +kernel

theorem input_510_length : input_510.length = 61 := by
  decide +kernel

theorem sort_510_correct :
    KernelSort.sortFuel wordLE 15429 input_510 = output_510 := by
  decide +kernel


end ThomGame.Lambda.Certificate
