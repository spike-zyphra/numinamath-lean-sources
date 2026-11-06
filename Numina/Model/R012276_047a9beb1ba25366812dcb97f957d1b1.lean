import Mathlib

theorem algebra_1120 (mph t d : ℚ) (hlate : 40 * (t + 3 / 60) = d) (hearly : 60 * (t - 3 / 60) = d) (hmph : mph * t = d) : mph = 48 := by 
  have eq1 : 40 * (t + 3 / 60) = d := hlate
  have eq2 : 60 * (t - 3 / 60) = d := hearly
  have ht : t = 1 / 4 := by
    linarith [eq1, eq2]
  have hd : d = 12 := by 
    rw [show t = 1/4 by linarith [eq1, eq2]] at eq1
    linarith
  rw [show t = 1/4 by linarith [eq1, eq2], show d = 12 by linarith [eq1, eq2] ] at hmph
  field_simp at hmph
  linarith