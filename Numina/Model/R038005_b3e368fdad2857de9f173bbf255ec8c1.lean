import Mathlib

theorem inequalities_304753 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    3 / Real.sqrt (a ^ 2 + 1) + 4 / Real.sqrt (b ^ 2 + 1) + 12 / Real.sqrt (c ^ 2 + 1) < 39 / 2 := by

  have h1 : 3 / Real.sqrt (a ^ 2 + 1) < 3 := by
    have ha3 : Real.sqrt (a ^ 2 + 1) > 1 := by
      have h2 : 1 < a ^ 2 + 1 := by nlinarith
      have h3 : Real.sqrt 1 < Real.sqrt (a ^ 2 + 1) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have h4 : Real.sqrt 1 = 1 := Real.sqrt_one
      linarith [h3, h4]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

  have h2 : 4 / Real.sqrt (b ^ 2 + 1) < 4 := by
    have hb3 : Real.sqrt (b ^ 2 + 1) > 1 := by
      have h2 : 1 < b ^ 2 + 1 := by nlinarith
      have h3 : Real.sqrt 1 < Real.sqrt (b ^ 2 + 1) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have h4 : Real.sqrt 1 = 1 := Real.sqrt_one
      linarith [h3, h4]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

  have h3 : 12 / Real.sqrt (c ^ 2 + 1) < 12 := by
    have hc3 : Real.sqrt (c ^ 2 + 1) > 1 := by
      have h2 : 1 < c ^ 2 + 1 := by nlinarith
      have h3 : Real.sqrt 1 < Real.sqrt (c ^ 2 + 1) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have h4 : Real.sqrt 1 = 1 := Real.sqrt_one
      linarith [h3, h4]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

  have h4 : 3 / Real.sqrt (a ^ 2 + 1) + 4 / Real.sqrt (b ^ 2 + 1) + 12 / Real.sqrt (c ^ 2 + 1) < 19 := by
    linarith [h1, h2, h3]

  linarith