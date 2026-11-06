import Mathlib

theorem algebra_288122 (d w z : ℝ) (hw : 0 < w) (hz : 0 < z) (h1 : d / w = d / z + 30 / 60)
    (h2 : d / z = d / w + 20 / 60) :
    (d - z * 20) / (w - z) = 40 := by
  have h3 : d / w - d / z = 30 / 60 := by linarith
  have h4 : d / z - d / w = 20 / 60 := by linarith
  have h5 : (d / w - d / z) + (d / z - d / w) = 0 := by ring
  have h6 : (d / w - d / z) + (d / z - d / w) = 50 / 60 := by linarith [h3, h4]
  linarith