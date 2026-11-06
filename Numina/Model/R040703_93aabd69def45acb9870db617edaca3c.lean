import Mathlib

theorem algebra_258716 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a + a * b) + 1 / (1 + b + b * c) + 1 / (1 + c + c * a) = 1 := by

  have h1 : c = 1 / (a * b) := by
    have h2 : a * b * c = 1 := habc
    field_simp [(show 0 < a * b by positivity)]
    nlinarith

  have eq1 : 1 / (1 + b + b * c) = a / (1 + a + a * b) := by
    rw [show c = 1 / (a * b) by linarith [h1]]
    field_simp [(show 0 < a * b by positivity)]
    <;> nlinarith [habc]

  have eq3 : 1 / (1 + c + c * a) = (a * b) / (1 + a + a * b) := by
    rw [show c = 1 / (a * b) by linarith [h1]]
    field_simp [(show 0 < a * b by positivity)]
    <;> nlinarith [habc]

  rw [eq1, eq3]

  have h2 : 1 / (1 + a + a * b) + a / (1 + a + a * b) + (a * b) / (1 + a + a * b) = 1 := by
    field_simp [(show 0 < a * b by positivity)]
    <;> nlinarith

  linarith [h2]