module

public import ThomGame.Certificates.LambdaSort08

/-! Each merge reuses the already proved child computations. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem input_007_length : input_007.length = 120 := by
  simp only [input_007, List.length_append, input_008_length, input_009_length]

theorem sort_007_correct :
    KernelSort.sortFuel wordLE 15430 input_007 = output_007 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_008 input_009 output_008 output_009 output_007
    input_008_length input_009_length (by decide) (by decide)
    sort_008_correct sort_009_correct (by decide +kernel)

theorem input_010_length : input_010.length = 121 := by
  simp only [input_010, List.length_append, input_011_length, input_012_length]

theorem sort_010_correct :
    KernelSort.sortFuel wordLE 15430 input_010 = output_010 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_011 input_012 output_011 output_012 output_010
    input_011_length input_012_length (by decide) (by decide)
    sort_011_correct sort_012_correct (by decide +kernel)

theorem input_014_length : input_014.length = 120 := by
  simp only [input_014, List.length_append, input_015_length, input_016_length]

theorem sort_014_correct :
    KernelSort.sortFuel wordLE 15430 input_014 = output_014 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_015 input_016 output_015 output_016 output_014
    input_015_length input_016_length (by decide) (by decide)
    sort_015_correct sort_016_correct (by decide +kernel)

theorem input_017_length : input_017.length = 121 := by
  simp only [input_017, List.length_append, input_018_length, input_019_length]

theorem sort_017_correct :
    KernelSort.sortFuel wordLE 15430 input_017 = output_017 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_018 input_019 output_018 output_019 output_017
    input_018_length input_019_length (by decide) (by decide)
    sort_018_correct sort_019_correct (by decide +kernel)

theorem input_022_length : input_022.length = 120 := by
  simp only [input_022, List.length_append, input_023_length, input_024_length]

theorem sort_022_correct :
    KernelSort.sortFuel wordLE 15430 input_022 = output_022 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_023 input_024 output_023 output_024 output_022
    input_023_length input_024_length (by decide) (by decide)
    sort_023_correct sort_024_correct (by decide +kernel)

theorem input_025_length : input_025.length = 121 := by
  simp only [input_025, List.length_append, input_026_length, input_027_length]

theorem sort_025_correct :
    KernelSort.sortFuel wordLE 15430 input_025 = output_025 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_026 input_027 output_026 output_027 output_025
    input_026_length input_027_length (by decide) (by decide)
    sort_026_correct sort_027_correct (by decide +kernel)

theorem input_029_length : input_029.length = 120 := by
  simp only [input_029, List.length_append, input_030_length, input_031_length]

theorem sort_029_correct :
    KernelSort.sortFuel wordLE 15430 input_029 = output_029 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_030 input_031 output_030 output_031 output_029
    input_030_length input_031_length (by decide) (by decide)
    sort_030_correct sort_031_correct (by decide +kernel)

theorem input_032_length : input_032.length = 121 := by
  simp only [input_032, List.length_append, input_033_length, input_034_length]

theorem sort_032_correct :
    KernelSort.sortFuel wordLE 15430 input_032 = output_032 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_033 input_034 output_033 output_034 output_032
    input_033_length input_034_length (by decide) (by decide)
    sort_033_correct sort_034_correct (by decide +kernel)

theorem input_038_length : input_038.length = 120 := by
  simp only [input_038, List.length_append, input_039_length, input_040_length]

theorem sort_038_correct :
    KernelSort.sortFuel wordLE 15430 input_038 = output_038 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_039 input_040 output_039 output_040 output_038
    input_039_length input_040_length (by decide) (by decide)
    sort_039_correct sort_040_correct (by decide +kernel)

theorem input_041_length : input_041.length = 121 := by
  simp only [input_041, List.length_append, input_042_length, input_043_length]

theorem sort_041_correct :
    KernelSort.sortFuel wordLE 15430 input_041 = output_041 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_042 input_043 output_042 output_043 output_041
    input_042_length input_043_length (by decide) (by decide)
    sort_042_correct sort_043_correct (by decide +kernel)

theorem input_045_length : input_045.length = 120 := by
  simp only [input_045, List.length_append, input_046_length, input_047_length]

theorem sort_045_correct :
    KernelSort.sortFuel wordLE 15430 input_045 = output_045 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_046 input_047 output_046 output_047 output_045
    input_046_length input_047_length (by decide) (by decide)
    sort_046_correct sort_047_correct (by decide +kernel)

theorem input_048_length : input_048.length = 121 := by
  simp only [input_048, List.length_append, input_049_length, input_050_length]

theorem sort_048_correct :
    KernelSort.sortFuel wordLE 15430 input_048 = output_048 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_049 input_050 output_049 output_050 output_048
    input_049_length input_050_length (by decide) (by decide)
    sort_049_correct sort_050_correct (by decide +kernel)

theorem input_053_length : input_053.length = 120 := by
  simp only [input_053, List.length_append, input_054_length, input_055_length]

theorem sort_053_correct :
    KernelSort.sortFuel wordLE 15430 input_053 = output_053 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_054 input_055 output_054 output_055 output_053
    input_054_length input_055_length (by decide) (by decide)
    sort_054_correct sort_055_correct (by decide +kernel)

theorem input_056_length : input_056.length = 121 := by
  simp only [input_056, List.length_append, input_057_length, input_058_length]

theorem sort_056_correct :
    KernelSort.sortFuel wordLE 15430 input_056 = output_056 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_057 input_058 output_057 output_058 output_056
    input_057_length input_058_length (by decide) (by decide)
    sort_057_correct sort_058_correct (by decide +kernel)

theorem input_060_length : input_060.length = 121 := by
  simp only [input_060, List.length_append, input_061_length, input_062_length]

theorem sort_060_correct :
    KernelSort.sortFuel wordLE 15430 input_060 = output_060 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_061 input_062 output_061 output_062 output_060
    input_061_length input_062_length (by decide) (by decide)
    sort_061_correct sort_062_correct (by decide +kernel)

theorem input_063_length : input_063.length = 121 := by
  simp only [input_063, List.length_append, input_064_length, input_065_length]

theorem sort_063_correct :
    KernelSort.sortFuel wordLE 15430 input_063 = output_063 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_064 input_065 output_064 output_065 output_063
    input_064_length input_065_length (by decide) (by decide)
    sort_064_correct sort_065_correct (by decide +kernel)

theorem input_070_length : input_070.length = 120 := by
  simp only [input_070, List.length_append, input_071_length, input_072_length]

theorem sort_070_correct :
    KernelSort.sortFuel wordLE 15430 input_070 = output_070 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_071 input_072 output_071 output_072 output_070
    input_071_length input_072_length (by decide) (by decide)
    sort_071_correct sort_072_correct (by decide +kernel)

theorem input_073_length : input_073.length = 121 := by
  simp only [input_073, List.length_append, input_074_length, input_075_length]

theorem sort_073_correct :
    KernelSort.sortFuel wordLE 15430 input_073 = output_073 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_074 input_075 output_074 output_075 output_073
    input_074_length input_075_length (by decide) (by decide)
    sort_074_correct sort_075_correct (by decide +kernel)

theorem input_077_length : input_077.length = 120 := by
  simp only [input_077, List.length_append, input_078_length, input_079_length]

theorem sort_077_correct :
    KernelSort.sortFuel wordLE 15430 input_077 = output_077 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_078 input_079 output_078 output_079 output_077
    input_078_length input_079_length (by decide) (by decide)
    sort_078_correct sort_079_correct (by decide +kernel)

theorem input_080_length : input_080.length = 121 := by
  simp only [input_080, List.length_append, input_081_length, input_082_length]

theorem sort_080_correct :
    KernelSort.sortFuel wordLE 15430 input_080 = output_080 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_081 input_082 output_081 output_082 output_080
    input_081_length input_082_length (by decide) (by decide)
    sort_081_correct sort_082_correct (by decide +kernel)

theorem input_085_length : input_085.length = 120 := by
  simp only [input_085, List.length_append, input_086_length, input_087_length]

theorem sort_085_correct :
    KernelSort.sortFuel wordLE 15430 input_085 = output_085 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_086 input_087 output_086 output_087 output_085
    input_086_length input_087_length (by decide) (by decide)
    sort_086_correct sort_087_correct (by decide +kernel)

theorem input_088_length : input_088.length = 121 := by
  simp only [input_088, List.length_append, input_089_length, input_090_length]

theorem sort_088_correct :
    KernelSort.sortFuel wordLE 15430 input_088 = output_088 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_089 input_090 output_089 output_090 output_088
    input_089_length input_090_length (by decide) (by decide)
    sort_089_correct sort_090_correct (by decide +kernel)

theorem input_092_length : input_092.length = 121 := by
  simp only [input_092, List.length_append, input_093_length, input_094_length]

theorem sort_092_correct :
    KernelSort.sortFuel wordLE 15430 input_092 = output_092 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_093 input_094 output_093 output_094 output_092
    input_093_length input_094_length (by decide) (by decide)
    sort_093_correct sort_094_correct (by decide +kernel)

theorem input_095_length : input_095.length = 121 := by
  simp only [input_095, List.length_append, input_096_length, input_097_length]

theorem sort_095_correct :
    KernelSort.sortFuel wordLE 15430 input_095 = output_095 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_096 input_097 output_096 output_097 output_095
    input_096_length input_097_length (by decide) (by decide)
    sort_096_correct sort_097_correct (by decide +kernel)

theorem input_101_length : input_101.length = 120 := by
  simp only [input_101, List.length_append, input_102_length, input_103_length]

theorem sort_101_correct :
    KernelSort.sortFuel wordLE 15430 input_101 = output_101 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_102 input_103 output_102 output_103 output_101
    input_102_length input_103_length (by decide) (by decide)
    sort_102_correct sort_103_correct (by decide +kernel)

theorem input_104_length : input_104.length = 121 := by
  simp only [input_104, List.length_append, input_105_length, input_106_length]

theorem sort_104_correct :
    KernelSort.sortFuel wordLE 15430 input_104 = output_104 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_105 input_106 output_105 output_106 output_104
    input_105_length input_106_length (by decide) (by decide)
    sort_105_correct sort_106_correct (by decide +kernel)

theorem input_108_length : input_108.length = 120 := by
  simp only [input_108, List.length_append, input_109_length, input_110_length]

theorem sort_108_correct :
    KernelSort.sortFuel wordLE 15430 input_108 = output_108 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_109 input_110 output_109 output_110 output_108
    input_109_length input_110_length (by decide) (by decide)
    sort_109_correct sort_110_correct (by decide +kernel)

theorem input_111_length : input_111.length = 121 := by
  simp only [input_111, List.length_append, input_112_length, input_113_length]

theorem sort_111_correct :
    KernelSort.sortFuel wordLE 15430 input_111 = output_111 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_112 input_113 output_112 output_113 output_111
    input_112_length input_113_length (by decide) (by decide)
    sort_112_correct sort_113_correct (by decide +kernel)

theorem input_116_length : input_116.length = 120 := by
  simp only [input_116, List.length_append, input_117_length, input_118_length]

theorem sort_116_correct :
    KernelSort.sortFuel wordLE 15430 input_116 = output_116 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_117 input_118 output_117 output_118 output_116
    input_117_length input_118_length (by decide) (by decide)
    sort_117_correct sort_118_correct (by decide +kernel)

theorem input_119_length : input_119.length = 121 := by
  simp only [input_119, List.length_append, input_120_length, input_121_length]

theorem sort_119_correct :
    KernelSort.sortFuel wordLE 15430 input_119 = output_119 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_120 input_121 output_120 output_121 output_119
    input_120_length input_121_length (by decide) (by decide)
    sort_120_correct sort_121_correct (by decide +kernel)

theorem input_123_length : input_123.length = 121 := by
  simp only [input_123, List.length_append, input_124_length, input_125_length]

theorem sort_123_correct :
    KernelSort.sortFuel wordLE 15430 input_123 = output_123 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_124 input_125 output_124 output_125 output_123
    input_124_length input_125_length (by decide) (by decide)
    sort_124_correct sort_125_correct (by decide +kernel)

theorem input_126_length : input_126.length = 121 := by
  simp only [input_126, List.length_append, input_127_length, input_128_length]

theorem sort_126_correct :
    KernelSort.sortFuel wordLE 15430 input_126 = output_126 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_127 input_128 output_127 output_128 output_126
    input_127_length input_128_length (by decide) (by decide)
    sort_127_correct sort_128_correct (by decide +kernel)

theorem input_134_length : input_134.length = 120 := by
  simp only [input_134, List.length_append, input_135_length, input_136_length]

theorem sort_134_correct :
    KernelSort.sortFuel wordLE 15430 input_134 = output_134 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_135 input_136 output_135 output_136 output_134
    input_135_length input_136_length (by decide) (by decide)
    sort_135_correct sort_136_correct (by decide +kernel)

theorem input_137_length : input_137.length = 121 := by
  simp only [input_137, List.length_append, input_138_length, input_139_length]

theorem sort_137_correct :
    KernelSort.sortFuel wordLE 15430 input_137 = output_137 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_138 input_139 output_138 output_139 output_137
    input_138_length input_139_length (by decide) (by decide)
    sort_138_correct sort_139_correct (by decide +kernel)

theorem input_141_length : input_141.length = 120 := by
  simp only [input_141, List.length_append, input_142_length, input_143_length]

theorem sort_141_correct :
    KernelSort.sortFuel wordLE 15430 input_141 = output_141 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_142 input_143 output_142 output_143 output_141
    input_142_length input_143_length (by decide) (by decide)
    sort_142_correct sort_143_correct (by decide +kernel)

theorem input_144_length : input_144.length = 121 := by
  simp only [input_144, List.length_append, input_145_length, input_146_length]

theorem sort_144_correct :
    KernelSort.sortFuel wordLE 15430 input_144 = output_144 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_145 input_146 output_145 output_146 output_144
    input_145_length input_146_length (by decide) (by decide)
    sort_145_correct sort_146_correct (by decide +kernel)

theorem input_149_length : input_149.length = 120 := by
  simp only [input_149, List.length_append, input_150_length, input_151_length]

theorem sort_149_correct :
    KernelSort.sortFuel wordLE 15430 input_149 = output_149 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_150 input_151 output_150 output_151 output_149
    input_150_length input_151_length (by decide) (by decide)
    sort_150_correct sort_151_correct (by decide +kernel)

theorem input_152_length : input_152.length = 121 := by
  simp only [input_152, List.length_append, input_153_length, input_154_length]

theorem sort_152_correct :
    KernelSort.sortFuel wordLE 15430 input_152 = output_152 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_153 input_154 output_153 output_154 output_152
    input_153_length input_154_length (by decide) (by decide)
    sort_153_correct sort_154_correct (by decide +kernel)

theorem input_156_length : input_156.length = 120 := by
  simp only [input_156, List.length_append, input_157_length, input_158_length]

theorem sort_156_correct :
    KernelSort.sortFuel wordLE 15430 input_156 = output_156 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_157 input_158 output_157 output_158 output_156
    input_157_length input_158_length (by decide) (by decide)
    sort_157_correct sort_158_correct (by decide +kernel)

theorem input_159_length : input_159.length = 121 := by
  simp only [input_159, List.length_append, input_160_length, input_161_length]

theorem sort_159_correct :
    KernelSort.sortFuel wordLE 15430 input_159 = output_159 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_160 input_161 output_160 output_161 output_159
    input_160_length input_161_length (by decide) (by decide)
    sort_160_correct sort_161_correct (by decide +kernel)

theorem input_165_length : input_165.length = 120 := by
  simp only [input_165, List.length_append, input_166_length, input_167_length]

theorem sort_165_correct :
    KernelSort.sortFuel wordLE 15430 input_165 = output_165 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_166 input_167 output_166 output_167 output_165
    input_166_length input_167_length (by decide) (by decide)
    sort_166_correct sort_167_correct (by decide +kernel)

theorem input_168_length : input_168.length = 121 := by
  simp only [input_168, List.length_append, input_169_length, input_170_length]

theorem sort_168_correct :
    KernelSort.sortFuel wordLE 15430 input_168 = output_168 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_169 input_170 output_169 output_170 output_168
    input_169_length input_170_length (by decide) (by decide)
    sort_169_correct sort_170_correct (by decide +kernel)

theorem input_172_length : input_172.length = 120 := by
  simp only [input_172, List.length_append, input_173_length, input_174_length]

theorem sort_172_correct :
    KernelSort.sortFuel wordLE 15430 input_172 = output_172 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_173 input_174 output_173 output_174 output_172
    input_173_length input_174_length (by decide) (by decide)
    sort_173_correct sort_174_correct (by decide +kernel)

theorem input_175_length : input_175.length = 121 := by
  simp only [input_175, List.length_append, input_176_length, input_177_length]

theorem sort_175_correct :
    KernelSort.sortFuel wordLE 15430 input_175 = output_175 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_176 input_177 output_176 output_177 output_175
    input_176_length input_177_length (by decide) (by decide)
    sort_176_correct sort_177_correct (by decide +kernel)

theorem input_180_length : input_180.length = 120 := by
  simp only [input_180, List.length_append, input_181_length, input_182_length]

theorem sort_180_correct :
    KernelSort.sortFuel wordLE 15430 input_180 = output_180 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_181 input_182 output_181 output_182 output_180
    input_181_length input_182_length (by decide) (by decide)
    sort_181_correct sort_182_correct (by decide +kernel)

theorem input_183_length : input_183.length = 121 := by
  simp only [input_183, List.length_append, input_184_length, input_185_length]

theorem sort_183_correct :
    KernelSort.sortFuel wordLE 15430 input_183 = output_183 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_184 input_185 output_184 output_185 output_183
    input_184_length input_185_length (by decide) (by decide)
    sort_184_correct sort_185_correct (by decide +kernel)

theorem input_187_length : input_187.length = 121 := by
  simp only [input_187, List.length_append, input_188_length, input_189_length]

theorem sort_187_correct :
    KernelSort.sortFuel wordLE 15430 input_187 = output_187 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_188 input_189 output_188 output_189 output_187
    input_188_length input_189_length (by decide) (by decide)
    sort_188_correct sort_189_correct (by decide +kernel)

theorem input_190_length : input_190.length = 121 := by
  simp only [input_190, List.length_append, input_191_length, input_192_length]

theorem sort_190_correct :
    KernelSort.sortFuel wordLE 15430 input_190 = output_190 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_191 input_192 output_191 output_192 output_190
    input_191_length input_192_length (by decide) (by decide)
    sort_191_correct sort_192_correct (by decide +kernel)

theorem input_197_length : input_197.length = 120 := by
  simp only [input_197, List.length_append, input_198_length, input_199_length]

theorem sort_197_correct :
    KernelSort.sortFuel wordLE 15430 input_197 = output_197 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_198 input_199 output_198 output_199 output_197
    input_198_length input_199_length (by decide) (by decide)
    sort_198_correct sort_199_correct (by decide +kernel)

theorem input_200_length : input_200.length = 121 := by
  simp only [input_200, List.length_append, input_201_length, input_202_length]

theorem sort_200_correct :
    KernelSort.sortFuel wordLE 15430 input_200 = output_200 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_201 input_202 output_201 output_202 output_200
    input_201_length input_202_length (by decide) (by decide)
    sort_201_correct sort_202_correct (by decide +kernel)

theorem input_204_length : input_204.length = 120 := by
  simp only [input_204, List.length_append, input_205_length, input_206_length]

theorem sort_204_correct :
    KernelSort.sortFuel wordLE 15430 input_204 = output_204 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_205 input_206 output_205 output_206 output_204
    input_205_length input_206_length (by decide) (by decide)
    sort_205_correct sort_206_correct (by decide +kernel)

theorem input_207_length : input_207.length = 121 := by
  simp only [input_207, List.length_append, input_208_length, input_209_length]

theorem sort_207_correct :
    KernelSort.sortFuel wordLE 15430 input_207 = output_207 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_208 input_209 output_208 output_209 output_207
    input_208_length input_209_length (by decide) (by decide)
    sort_208_correct sort_209_correct (by decide +kernel)

theorem input_212_length : input_212.length = 120 := by
  simp only [input_212, List.length_append, input_213_length, input_214_length]

theorem sort_212_correct :
    KernelSort.sortFuel wordLE 15430 input_212 = output_212 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_213 input_214 output_213 output_214 output_212
    input_213_length input_214_length (by decide) (by decide)
    sort_213_correct sort_214_correct (by decide +kernel)

theorem input_215_length : input_215.length = 121 := by
  simp only [input_215, List.length_append, input_216_length, input_217_length]

theorem sort_215_correct :
    KernelSort.sortFuel wordLE 15430 input_215 = output_215 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_216 input_217 output_216 output_217 output_215
    input_216_length input_217_length (by decide) (by decide)
    sort_216_correct sort_217_correct (by decide +kernel)

theorem input_219_length : input_219.length = 121 := by
  simp only [input_219, List.length_append, input_220_length, input_221_length]

theorem sort_219_correct :
    KernelSort.sortFuel wordLE 15430 input_219 = output_219 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_220 input_221 output_220 output_221 output_219
    input_220_length input_221_length (by decide) (by decide)
    sort_220_correct sort_221_correct (by decide +kernel)

theorem input_222_length : input_222.length = 121 := by
  simp only [input_222, List.length_append, input_223_length, input_224_length]

theorem sort_222_correct :
    KernelSort.sortFuel wordLE 15430 input_222 = output_222 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_223 input_224 output_223 output_224 output_222
    input_223_length input_224_length (by decide) (by decide)
    sort_223_correct sort_224_correct (by decide +kernel)

theorem input_228_length : input_228.length = 120 := by
  simp only [input_228, List.length_append, input_229_length, input_230_length]

theorem sort_228_correct :
    KernelSort.sortFuel wordLE 15430 input_228 = output_228 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_229 input_230 output_229 output_230 output_228
    input_229_length input_230_length (by decide) (by decide)
    sort_229_correct sort_230_correct (by decide +kernel)

theorem input_231_length : input_231.length = 121 := by
  simp only [input_231, List.length_append, input_232_length, input_233_length]

theorem sort_231_correct :
    KernelSort.sortFuel wordLE 15430 input_231 = output_231 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_232 input_233 output_232 output_233 output_231
    input_232_length input_233_length (by decide) (by decide)
    sort_232_correct sort_233_correct (by decide +kernel)

theorem input_235_length : input_235.length = 120 := by
  simp only [input_235, List.length_append, input_236_length, input_237_length]

theorem sort_235_correct :
    KernelSort.sortFuel wordLE 15430 input_235 = output_235 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_236 input_237 output_236 output_237 output_235
    input_236_length input_237_length (by decide) (by decide)
    sort_236_correct sort_237_correct (by decide +kernel)

theorem input_238_length : input_238.length = 121 := by
  simp only [input_238, List.length_append, input_239_length, input_240_length]

theorem sort_238_correct :
    KernelSort.sortFuel wordLE 15430 input_238 = output_238 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_239 input_240 output_239 output_240 output_238
    input_239_length input_240_length (by decide) (by decide)
    sort_239_correct sort_240_correct (by decide +kernel)

theorem input_243_length : input_243.length = 120 := by
  simp only [input_243, List.length_append, input_244_length, input_245_length]

theorem sort_243_correct :
    KernelSort.sortFuel wordLE 15430 input_243 = output_243 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_244 input_245 output_244 output_245 output_243
    input_244_length input_245_length (by decide) (by decide)
    sort_244_correct sort_245_correct (by decide +kernel)

theorem input_246_length : input_246.length = 121 := by
  simp only [input_246, List.length_append, input_247_length, input_248_length]

theorem sort_246_correct :
    KernelSort.sortFuel wordLE 15430 input_246 = output_246 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_247 input_248 output_247 output_248 output_246
    input_247_length input_248_length (by decide) (by decide)
    sort_247_correct sort_248_correct (by decide +kernel)

theorem input_250_length : input_250.length = 121 := by
  simp only [input_250, List.length_append, input_251_length, input_252_length]

theorem sort_250_correct :
    KernelSort.sortFuel wordLE 15430 input_250 = output_250 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_251 input_252 output_251 output_252 output_250
    input_251_length input_252_length (by decide) (by decide)
    sort_251_correct sort_252_correct (by decide +kernel)

theorem input_253_length : input_253.length = 121 := by
  simp only [input_253, List.length_append, input_254_length, input_255_length]

theorem sort_253_correct :
    KernelSort.sortFuel wordLE 15430 input_253 = output_253 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_254 input_255 output_254 output_255 output_253
    input_254_length input_255_length (by decide) (by decide)
    sort_254_correct sort_255_correct (by decide +kernel)

theorem input_262_length : input_262.length = 120 := by
  simp only [input_262, List.length_append, input_263_length, input_264_length]

theorem sort_262_correct :
    KernelSort.sortFuel wordLE 15430 input_262 = output_262 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_263 input_264 output_263 output_264 output_262
    input_263_length input_264_length (by decide) (by decide)
    sort_263_correct sort_264_correct (by decide +kernel)

theorem input_265_length : input_265.length = 121 := by
  simp only [input_265, List.length_append, input_266_length, input_267_length]

theorem sort_265_correct :
    KernelSort.sortFuel wordLE 15430 input_265 = output_265 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_266 input_267 output_266 output_267 output_265
    input_266_length input_267_length (by decide) (by decide)
    sort_266_correct sort_267_correct (by decide +kernel)

theorem input_269_length : input_269.length = 120 := by
  simp only [input_269, List.length_append, input_270_length, input_271_length]

theorem sort_269_correct :
    KernelSort.sortFuel wordLE 15430 input_269 = output_269 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_270 input_271 output_270 output_271 output_269
    input_270_length input_271_length (by decide) (by decide)
    sort_270_correct sort_271_correct (by decide +kernel)

theorem input_272_length : input_272.length = 121 := by
  simp only [input_272, List.length_append, input_273_length, input_274_length]

theorem sort_272_correct :
    KernelSort.sortFuel wordLE 15430 input_272 = output_272 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_273 input_274 output_273 output_274 output_272
    input_273_length input_274_length (by decide) (by decide)
    sort_273_correct sort_274_correct (by decide +kernel)

theorem input_277_length : input_277.length = 120 := by
  simp only [input_277, List.length_append, input_278_length, input_279_length]

theorem sort_277_correct :
    KernelSort.sortFuel wordLE 15430 input_277 = output_277 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_278 input_279 output_278 output_279 output_277
    input_278_length input_279_length (by decide) (by decide)
    sort_278_correct sort_279_correct (by decide +kernel)

theorem input_280_length : input_280.length = 121 := by
  simp only [input_280, List.length_append, input_281_length, input_282_length]

theorem sort_280_correct :
    KernelSort.sortFuel wordLE 15430 input_280 = output_280 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_281 input_282 output_281 output_282 output_280
    input_281_length input_282_length (by decide) (by decide)
    sort_281_correct sort_282_correct (by decide +kernel)

theorem input_284_length : input_284.length = 120 := by
  simp only [input_284, List.length_append, input_285_length, input_286_length]

theorem sort_284_correct :
    KernelSort.sortFuel wordLE 15430 input_284 = output_284 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_285 input_286 output_285 output_286 output_284
    input_285_length input_286_length (by decide) (by decide)
    sort_285_correct sort_286_correct (by decide +kernel)

theorem input_287_length : input_287.length = 121 := by
  simp only [input_287, List.length_append, input_288_length, input_289_length]

theorem sort_287_correct :
    KernelSort.sortFuel wordLE 15430 input_287 = output_287 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_288 input_289 output_288 output_289 output_287
    input_288_length input_289_length (by decide) (by decide)
    sort_288_correct sort_289_correct (by decide +kernel)

theorem input_293_length : input_293.length = 120 := by
  simp only [input_293, List.length_append, input_294_length, input_295_length]

theorem sort_293_correct :
    KernelSort.sortFuel wordLE 15430 input_293 = output_293 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_294 input_295 output_294 output_295 output_293
    input_294_length input_295_length (by decide) (by decide)
    sort_294_correct sort_295_correct (by decide +kernel)

theorem input_296_length : input_296.length = 121 := by
  simp only [input_296, List.length_append, input_297_length, input_298_length]

theorem sort_296_correct :
    KernelSort.sortFuel wordLE 15430 input_296 = output_296 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_297 input_298 output_297 output_298 output_296
    input_297_length input_298_length (by decide) (by decide)
    sort_297_correct sort_298_correct (by decide +kernel)

theorem input_300_length : input_300.length = 120 := by
  simp only [input_300, List.length_append, input_301_length, input_302_length]

theorem sort_300_correct :
    KernelSort.sortFuel wordLE 15430 input_300 = output_300 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_301 input_302 output_301 output_302 output_300
    input_301_length input_302_length (by decide) (by decide)
    sort_301_correct sort_302_correct (by decide +kernel)

theorem input_303_length : input_303.length = 121 := by
  simp only [input_303, List.length_append, input_304_length, input_305_length]

theorem sort_303_correct :
    KernelSort.sortFuel wordLE 15430 input_303 = output_303 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_304 input_305 output_304 output_305 output_303
    input_304_length input_305_length (by decide) (by decide)
    sort_304_correct sort_305_correct (by decide +kernel)

theorem input_308_length : input_308.length = 120 := by
  simp only [input_308, List.length_append, input_309_length, input_310_length]

theorem sort_308_correct :
    KernelSort.sortFuel wordLE 15430 input_308 = output_308 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_309 input_310 output_309 output_310 output_308
    input_309_length input_310_length (by decide) (by decide)
    sort_309_correct sort_310_correct (by decide +kernel)

theorem input_311_length : input_311.length = 121 := by
  simp only [input_311, List.length_append, input_312_length, input_313_length]

theorem sort_311_correct :
    KernelSort.sortFuel wordLE 15430 input_311 = output_311 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_312 input_313 output_312 output_313 output_311
    input_312_length input_313_length (by decide) (by decide)
    sort_312_correct sort_313_correct (by decide +kernel)

theorem input_315_length : input_315.length = 121 := by
  simp only [input_315, List.length_append, input_316_length, input_317_length]

theorem sort_315_correct :
    KernelSort.sortFuel wordLE 15430 input_315 = output_315 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_316 input_317 output_316 output_317 output_315
    input_316_length input_317_length (by decide) (by decide)
    sort_316_correct sort_317_correct (by decide +kernel)

theorem input_318_length : input_318.length = 121 := by
  simp only [input_318, List.length_append, input_319_length, input_320_length]

theorem sort_318_correct :
    KernelSort.sortFuel wordLE 15430 input_318 = output_318 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_319 input_320 output_319 output_320 output_318
    input_319_length input_320_length (by decide) (by decide)
    sort_319_correct sort_320_correct (by decide +kernel)

theorem input_325_length : input_325.length = 120 := by
  simp only [input_325, List.length_append, input_326_length, input_327_length]

theorem sort_325_correct :
    KernelSort.sortFuel wordLE 15430 input_325 = output_325 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_326 input_327 output_326 output_327 output_325
    input_326_length input_327_length (by decide) (by decide)
    sort_326_correct sort_327_correct (by decide +kernel)

theorem input_328_length : input_328.length = 121 := by
  simp only [input_328, List.length_append, input_329_length, input_330_length]

theorem sort_328_correct :
    KernelSort.sortFuel wordLE 15430 input_328 = output_328 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_329 input_330 output_329 output_330 output_328
    input_329_length input_330_length (by decide) (by decide)
    sort_329_correct sort_330_correct (by decide +kernel)

theorem input_332_length : input_332.length = 120 := by
  simp only [input_332, List.length_append, input_333_length, input_334_length]

theorem sort_332_correct :
    KernelSort.sortFuel wordLE 15430 input_332 = output_332 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_333 input_334 output_333 output_334 output_332
    input_333_length input_334_length (by decide) (by decide)
    sort_333_correct sort_334_correct (by decide +kernel)

theorem input_335_length : input_335.length = 121 := by
  simp only [input_335, List.length_append, input_336_length, input_337_length]

theorem sort_335_correct :
    KernelSort.sortFuel wordLE 15430 input_335 = output_335 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_336 input_337 output_336 output_337 output_335
    input_336_length input_337_length (by decide) (by decide)
    sort_336_correct sort_337_correct (by decide +kernel)

theorem input_340_length : input_340.length = 120 := by
  simp only [input_340, List.length_append, input_341_length, input_342_length]

theorem sort_340_correct :
    KernelSort.sortFuel wordLE 15430 input_340 = output_340 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_341 input_342 output_341 output_342 output_340
    input_341_length input_342_length (by decide) (by decide)
    sort_341_correct sort_342_correct (by decide +kernel)

theorem input_343_length : input_343.length = 121 := by
  simp only [input_343, List.length_append, input_344_length, input_345_length]

theorem sort_343_correct :
    KernelSort.sortFuel wordLE 15430 input_343 = output_343 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_344 input_345 output_344 output_345 output_343
    input_344_length input_345_length (by decide) (by decide)
    sort_344_correct sort_345_correct (by decide +kernel)

theorem input_347_length : input_347.length = 121 := by
  simp only [input_347, List.length_append, input_348_length, input_349_length]

theorem sort_347_correct :
    KernelSort.sortFuel wordLE 15430 input_347 = output_347 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_348 input_349 output_348 output_349 output_347
    input_348_length input_349_length (by decide) (by decide)
    sort_348_correct sort_349_correct (by decide +kernel)

theorem input_350_length : input_350.length = 121 := by
  simp only [input_350, List.length_append, input_351_length, input_352_length]

theorem sort_350_correct :
    KernelSort.sortFuel wordLE 15430 input_350 = output_350 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_351 input_352 output_351 output_352 output_350
    input_351_length input_352_length (by decide) (by decide)
    sort_351_correct sort_352_correct (by decide +kernel)

theorem input_356_length : input_356.length = 120 := by
  simp only [input_356, List.length_append, input_357_length, input_358_length]

theorem sort_356_correct :
    KernelSort.sortFuel wordLE 15430 input_356 = output_356 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_357 input_358 output_357 output_358 output_356
    input_357_length input_358_length (by decide) (by decide)
    sort_357_correct sort_358_correct (by decide +kernel)

theorem input_359_length : input_359.length = 121 := by
  simp only [input_359, List.length_append, input_360_length, input_361_length]

theorem sort_359_correct :
    KernelSort.sortFuel wordLE 15430 input_359 = output_359 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_360 input_361 output_360 output_361 output_359
    input_360_length input_361_length (by decide) (by decide)
    sort_360_correct sort_361_correct (by decide +kernel)

theorem input_363_length : input_363.length = 120 := by
  simp only [input_363, List.length_append, input_364_length, input_365_length]

theorem sort_363_correct :
    KernelSort.sortFuel wordLE 15430 input_363 = output_363 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_364 input_365 output_364 output_365 output_363
    input_364_length input_365_length (by decide) (by decide)
    sort_364_correct sort_365_correct (by decide +kernel)

theorem input_366_length : input_366.length = 121 := by
  simp only [input_366, List.length_append, input_367_length, input_368_length]

theorem sort_366_correct :
    KernelSort.sortFuel wordLE 15430 input_366 = output_366 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_367 input_368 output_367 output_368 output_366
    input_367_length input_368_length (by decide) (by decide)
    sort_367_correct sort_368_correct (by decide +kernel)

theorem input_371_length : input_371.length = 120 := by
  simp only [input_371, List.length_append, input_372_length, input_373_length]

theorem sort_371_correct :
    KernelSort.sortFuel wordLE 15430 input_371 = output_371 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_372 input_373 output_372 output_373 output_371
    input_372_length input_373_length (by decide) (by decide)
    sort_372_correct sort_373_correct (by decide +kernel)

theorem input_374_length : input_374.length = 121 := by
  simp only [input_374, List.length_append, input_375_length, input_376_length]

theorem sort_374_correct :
    KernelSort.sortFuel wordLE 15430 input_374 = output_374 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_375 input_376 output_375 output_376 output_374
    input_375_length input_376_length (by decide) (by decide)
    sort_375_correct sort_376_correct (by decide +kernel)

theorem input_378_length : input_378.length = 121 := by
  simp only [input_378, List.length_append, input_379_length, input_380_length]

theorem sort_378_correct :
    KernelSort.sortFuel wordLE 15430 input_378 = output_378 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_379 input_380 output_379 output_380 output_378
    input_379_length input_380_length (by decide) (by decide)
    sort_379_correct sort_380_correct (by decide +kernel)

theorem input_381_length : input_381.length = 121 := by
  simp only [input_381, List.length_append, input_382_length, input_383_length]

theorem sort_381_correct :
    KernelSort.sortFuel wordLE 15430 input_381 = output_381 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_382 input_383 output_382 output_383 output_381
    input_382_length input_383_length (by decide) (by decide)
    sort_382_correct sort_383_correct (by decide +kernel)

theorem input_389_length : input_389.length = 120 := by
  simp only [input_389, List.length_append, input_390_length, input_391_length]

theorem sort_389_correct :
    KernelSort.sortFuel wordLE 15430 input_389 = output_389 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_390 input_391 output_390 output_391 output_389
    input_390_length input_391_length (by decide) (by decide)
    sort_390_correct sort_391_correct (by decide +kernel)

theorem input_392_length : input_392.length = 121 := by
  simp only [input_392, List.length_append, input_393_length, input_394_length]

theorem sort_392_correct :
    KernelSort.sortFuel wordLE 15430 input_392 = output_392 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_393 input_394 output_393 output_394 output_392
    input_393_length input_394_length (by decide) (by decide)
    sort_393_correct sort_394_correct (by decide +kernel)

theorem input_396_length : input_396.length = 120 := by
  simp only [input_396, List.length_append, input_397_length, input_398_length]

theorem sort_396_correct :
    KernelSort.sortFuel wordLE 15430 input_396 = output_396 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_397 input_398 output_397 output_398 output_396
    input_397_length input_398_length (by decide) (by decide)
    sort_397_correct sort_398_correct (by decide +kernel)

theorem input_399_length : input_399.length = 121 := by
  simp only [input_399, List.length_append, input_400_length, input_401_length]

theorem sort_399_correct :
    KernelSort.sortFuel wordLE 15430 input_399 = output_399 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_400 input_401 output_400 output_401 output_399
    input_400_length input_401_length (by decide) (by decide)
    sort_400_correct sort_401_correct (by decide +kernel)

theorem input_404_length : input_404.length = 120 := by
  simp only [input_404, List.length_append, input_405_length, input_406_length]

theorem sort_404_correct :
    KernelSort.sortFuel wordLE 15430 input_404 = output_404 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_405 input_406 output_405 output_406 output_404
    input_405_length input_406_length (by decide) (by decide)
    sort_405_correct sort_406_correct (by decide +kernel)

theorem input_407_length : input_407.length = 121 := by
  simp only [input_407, List.length_append, input_408_length, input_409_length]

theorem sort_407_correct :
    KernelSort.sortFuel wordLE 15430 input_407 = output_407 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_408 input_409 output_408 output_409 output_407
    input_408_length input_409_length (by decide) (by decide)
    sort_408_correct sort_409_correct (by decide +kernel)

theorem input_411_length : input_411.length = 121 := by
  simp only [input_411, List.length_append, input_412_length, input_413_length]

theorem sort_411_correct :
    KernelSort.sortFuel wordLE 15430 input_411 = output_411 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_412 input_413 output_412 output_413 output_411
    input_412_length input_413_length (by decide) (by decide)
    sort_412_correct sort_413_correct (by decide +kernel)

theorem input_414_length : input_414.length = 121 := by
  simp only [input_414, List.length_append, input_415_length, input_416_length]

theorem sort_414_correct :
    KernelSort.sortFuel wordLE 15430 input_414 = output_414 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_415 input_416 output_415 output_416 output_414
    input_415_length input_416_length (by decide) (by decide)
    sort_415_correct sort_416_correct (by decide +kernel)

theorem input_420_length : input_420.length = 120 := by
  simp only [input_420, List.length_append, input_421_length, input_422_length]

theorem sort_420_correct :
    KernelSort.sortFuel wordLE 15430 input_420 = output_420 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_421 input_422 output_421 output_422 output_420
    input_421_length input_422_length (by decide) (by decide)
    sort_421_correct sort_422_correct (by decide +kernel)

theorem input_423_length : input_423.length = 121 := by
  simp only [input_423, List.length_append, input_424_length, input_425_length]

theorem sort_423_correct :
    KernelSort.sortFuel wordLE 15430 input_423 = output_423 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_424 input_425 output_424 output_425 output_423
    input_424_length input_425_length (by decide) (by decide)
    sort_424_correct sort_425_correct (by decide +kernel)

theorem input_427_length : input_427.length = 120 := by
  simp only [input_427, List.length_append, input_428_length, input_429_length]

theorem sort_427_correct :
    KernelSort.sortFuel wordLE 15430 input_427 = output_427 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_428 input_429 output_428 output_429 output_427
    input_428_length input_429_length (by decide) (by decide)
    sort_428_correct sort_429_correct (by decide +kernel)

theorem input_430_length : input_430.length = 121 := by
  simp only [input_430, List.length_append, input_431_length, input_432_length]

theorem sort_430_correct :
    KernelSort.sortFuel wordLE 15430 input_430 = output_430 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_431 input_432 output_431 output_432 output_430
    input_431_length input_432_length (by decide) (by decide)
    sort_431_correct sort_432_correct (by decide +kernel)

theorem input_435_length : input_435.length = 120 := by
  simp only [input_435, List.length_append, input_436_length, input_437_length]

theorem sort_435_correct :
    KernelSort.sortFuel wordLE 15430 input_435 = output_435 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_436 input_437 output_436 output_437 output_435
    input_436_length input_437_length (by decide) (by decide)
    sort_436_correct sort_437_correct (by decide +kernel)

theorem input_438_length : input_438.length = 121 := by
  simp only [input_438, List.length_append, input_439_length, input_440_length]

theorem sort_438_correct :
    KernelSort.sortFuel wordLE 15430 input_438 = output_438 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_439 input_440 output_439 output_440 output_438
    input_439_length input_440_length (by decide) (by decide)
    sort_439_correct sort_440_correct (by decide +kernel)

theorem input_442_length : input_442.length = 121 := by
  simp only [input_442, List.length_append, input_443_length, input_444_length]

theorem sort_442_correct :
    KernelSort.sortFuel wordLE 15430 input_442 = output_442 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_443 input_444 output_443 output_444 output_442
    input_443_length input_444_length (by decide) (by decide)
    sort_443_correct sort_444_correct (by decide +kernel)

theorem input_445_length : input_445.length = 121 := by
  simp only [input_445, List.length_append, input_446_length, input_447_length]

theorem sort_445_correct :
    KernelSort.sortFuel wordLE 15430 input_445 = output_445 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_446 input_447 output_446 output_447 output_445
    input_446_length input_447_length (by decide) (by decide)
    sort_446_correct sort_447_correct (by decide +kernel)

theorem input_452_length : input_452.length = 120 := by
  simp only [input_452, List.length_append, input_453_length, input_454_length]

theorem sort_452_correct :
    KernelSort.sortFuel wordLE 15430 input_452 = output_452 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_453 input_454 output_453 output_454 output_452
    input_453_length input_454_length (by decide) (by decide)
    sort_453_correct sort_454_correct (by decide +kernel)

theorem input_455_length : input_455.length = 121 := by
  simp only [input_455, List.length_append, input_456_length, input_457_length]

theorem sort_455_correct :
    KernelSort.sortFuel wordLE 15430 input_455 = output_455 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_456 input_457 output_456 output_457 output_455
    input_456_length input_457_length (by decide) (by decide)
    sort_456_correct sort_457_correct (by decide +kernel)

theorem input_459_length : input_459.length = 120 := by
  simp only [input_459, List.length_append, input_460_length, input_461_length]

theorem sort_459_correct :
    KernelSort.sortFuel wordLE 15430 input_459 = output_459 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_460 input_461 output_460 output_461 output_459
    input_460_length input_461_length (by decide) (by decide)
    sort_460_correct sort_461_correct (by decide +kernel)

theorem input_462_length : input_462.length = 121 := by
  simp only [input_462, List.length_append, input_463_length, input_464_length]

theorem sort_462_correct :
    KernelSort.sortFuel wordLE 15430 input_462 = output_462 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_463 input_464 output_463 output_464 output_462
    input_463_length input_464_length (by decide) (by decide)
    sort_463_correct sort_464_correct (by decide +kernel)

theorem input_467_length : input_467.length = 120 := by
  simp only [input_467, List.length_append, input_468_length, input_469_length]

theorem sort_467_correct :
    KernelSort.sortFuel wordLE 15430 input_467 = output_467 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_468 input_469 output_468 output_469 output_467
    input_468_length input_469_length (by decide) (by decide)
    sort_468_correct sort_469_correct (by decide +kernel)

theorem input_470_length : input_470.length = 121 := by
  simp only [input_470, List.length_append, input_471_length, input_472_length]

theorem sort_470_correct :
    KernelSort.sortFuel wordLE 15430 input_470 = output_470 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_471 input_472 output_471 output_472 output_470
    input_471_length input_472_length (by decide) (by decide)
    sort_471_correct sort_472_correct (by decide +kernel)

theorem input_474_length : input_474.length = 121 := by
  simp only [input_474, List.length_append, input_475_length, input_476_length]

theorem sort_474_correct :
    KernelSort.sortFuel wordLE 15430 input_474 = output_474 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_475 input_476 output_475 output_476 output_474
    input_475_length input_476_length (by decide) (by decide)
    sort_475_correct sort_476_correct (by decide +kernel)

theorem input_477_length : input_477.length = 121 := by
  simp only [input_477, List.length_append, input_478_length, input_479_length]

theorem sort_477_correct :
    KernelSort.sortFuel wordLE 15430 input_477 = output_477 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_478 input_479 output_478 output_479 output_477
    input_478_length input_479_length (by decide) (by decide)
    sort_478_correct sort_479_correct (by decide +kernel)

theorem input_483_length : input_483.length = 120 := by
  simp only [input_483, List.length_append, input_484_length, input_485_length]

theorem sort_483_correct :
    KernelSort.sortFuel wordLE 15430 input_483 = output_483 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_484 input_485 output_484 output_485 output_483
    input_484_length input_485_length (by decide) (by decide)
    sort_484_correct sort_485_correct (by decide +kernel)

theorem input_486_length : input_486.length = 121 := by
  simp only [input_486, List.length_append, input_487_length, input_488_length]

theorem sort_486_correct :
    KernelSort.sortFuel wordLE 15430 input_486 = output_486 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_487 input_488 output_487 output_488 output_486
    input_487_length input_488_length (by decide) (by decide)
    sort_487_correct sort_488_correct (by decide +kernel)

theorem input_490_length : input_490.length = 120 := by
  simp only [input_490, List.length_append, input_491_length, input_492_length]

theorem sort_490_correct :
    KernelSort.sortFuel wordLE 15430 input_490 = output_490 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_491 input_492 output_491 output_492 output_490
    input_491_length input_492_length (by decide) (by decide)
    sort_491_correct sort_492_correct (by decide +kernel)

theorem input_493_length : input_493.length = 121 := by
  simp only [input_493, List.length_append, input_494_length, input_495_length]

theorem sort_493_correct :
    KernelSort.sortFuel wordLE 15430 input_493 = output_493 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_494 input_495 output_494 output_495 output_493
    input_494_length input_495_length (by decide) (by decide)
    sort_494_correct sort_495_correct (by decide +kernel)

theorem input_498_length : input_498.length = 120 := by
  simp only [input_498, List.length_append, input_499_length, input_500_length]

theorem sort_498_correct :
    KernelSort.sortFuel wordLE 15430 input_498 = output_498 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 60
    input_499 input_500 output_499 output_500 output_498
    input_499_length input_500_length (by decide) (by decide)
    sort_499_correct sort_500_correct (by decide +kernel)

theorem input_501_length : input_501.length = 121 := by
  simp only [input_501, List.length_append, input_502_length, input_503_length]

theorem sort_501_correct :
    KernelSort.sortFuel wordLE 15430 input_501 = output_501 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_502 input_503 output_502 output_503 output_501
    input_502_length input_503_length (by decide) (by decide)
    sort_502_correct sort_503_correct (by decide +kernel)

theorem input_505_length : input_505.length = 121 := by
  simp only [input_505, List.length_append, input_506_length, input_507_length]

theorem sort_505_correct :
    KernelSort.sortFuel wordLE 15430 input_505 = output_505 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_506 input_507 output_506 output_507 output_505
    input_506_length input_507_length (by decide) (by decide)
    sort_506_correct sort_507_correct (by decide +kernel)

theorem input_508_length : input_508.length = 121 := by
  simp only [input_508, List.length_append, input_509_length, input_510_length]

theorem sort_508_correct :
    KernelSort.sortFuel wordLE 15430 input_508 = output_508 := by
  exact KernelSort.sortFuel_step wordLE 15429 60 61
    input_509 input_510 output_509 output_510 output_508
    input_509_length input_510_length (by decide) (by decide)
    sort_509_correct sort_510_correct (by decide +kernel)


end ThomGame.Lambda.Certificate
