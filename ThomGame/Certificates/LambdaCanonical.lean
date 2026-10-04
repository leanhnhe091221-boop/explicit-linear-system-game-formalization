module

public import ThomGame.Certificates.LambdaRaw
public import ThomGame.Certificates.LambdaCanonical00
public import ThomGame.Certificates.LambdaCanonical01
public import ThomGame.Certificates.LambdaCanonical02
public import ThomGame.Certificates.LambdaCanonical03
public import ThomGame.Certificates.LambdaCanonical04
public import ThomGame.Certificates.LambdaCanonical05
public import ThomGame.Certificates.LambdaCanonical06
public import ThomGame.Certificates.LambdaCanonical07
public import ThomGame.Certificates.LambdaCanonical08
public import ThomGame.Certificates.LambdaCanonical09
public import ThomGame.Certificates.LambdaCanonical10
public import ThomGame.Certificates.LambdaCanonical11
public import ThomGame.Certificates.LambdaCanonical12
public import ThomGame.Certificates.LambdaCanonical13
public import ThomGame.Certificates.LambdaCanonical14
public import ThomGame.Certificates.LambdaCanonical15

/-! Assembly of the checked canonicalization chunks. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_eq_table :
    (rawRelators.map canonical).filter (fun r => !r.isEmpty) = cleanTable := by
  rw [raw_eq_table]
  simp only [rawTable, List.map_append, List.filter_append,
    clean_000_correct,
    clean_001_correct,
    clean_002_correct,
    clean_003_correct,
    clean_004_correct,
    clean_005_correct,
    clean_006_correct,
    clean_007_correct,
    clean_008_correct,
    clean_009_correct,
    clean_010_correct,
    clean_011_correct,
    clean_012_correct,
    clean_013_correct,
    clean_014_correct,
    clean_015_correct,
    clean_016_correct,
    clean_017_correct,
    clean_018_correct,
    clean_019_correct,
    clean_020_correct,
    clean_021_correct,
    clean_022_correct,
    clean_023_correct,
    clean_024_correct,
    clean_025_correct,
    clean_026_correct,
    clean_027_correct,
    clean_028_correct,
    clean_029_correct,
    clean_030_correct,
    clean_031_correct,
    clean_032_correct,
    clean_033_correct,
    clean_034_correct,
    clean_035_correct,
    clean_036_correct,
    clean_037_correct,
    clean_038_correct,
    clean_039_correct,
    clean_040_correct,
    clean_041_correct,
    clean_042_correct,
    clean_043_correct,
    clean_044_correct,
    clean_045_correct,
    clean_046_correct,
    clean_047_correct,
    clean_048_correct,
    clean_049_correct,
    clean_050_correct,
    clean_051_correct,
    clean_052_correct,
    clean_053_correct,
    clean_054_correct,
    clean_055_correct,
    clean_056_correct,
    clean_057_correct,
    clean_058_correct,
    clean_059_correct,
    clean_060_correct,
    clean_061_correct,
    clean_062_correct,
    clean_063_correct,
    clean_064_correct,
    clean_065_correct,
    clean_066_correct,
    clean_067_correct,
    clean_068_correct,
    clean_069_correct,
    clean_070_correct,
    clean_071_correct,
    clean_072_correct,
    clean_073_correct,
    clean_074_correct,
    clean_075_correct,
    clean_076_correct,
    clean_077_correct,
    clean_078_correct,
    clean_079_correct,
    clean_080_correct,
    clean_081_correct,
    clean_082_correct,
    clean_083_correct,
    clean_084_correct,
    clean_085_correct,
    clean_086_correct,
    clean_087_correct,
    clean_088_correct,
    clean_089_correct,
    clean_090_correct,
    clean_091_correct,
    clean_092_correct,
    clean_093_correct,
    clean_094_correct,
    clean_095_correct,
    clean_096_correct,
    clean_097_correct,
    clean_098_correct,
    clean_099_correct,
    clean_100_correct,
    clean_101_correct,
    clean_102_correct,
    clean_103_correct,
    clean_104_correct,
    clean_105_correct,
    clean_106_correct,
    clean_107_correct,
    clean_108_correct,
    clean_109_correct,
    clean_110_correct,
    clean_111_correct,
    clean_112_correct,
    clean_113_correct,
    clean_114_correct,
    clean_115_correct,
    clean_116_correct,
    clean_117_correct,
    clean_118_correct,
    clean_119_correct,
    clean_120_correct,
    clean_121_correct, cleanTable]

end ThomGame.Lambda.Certificate
