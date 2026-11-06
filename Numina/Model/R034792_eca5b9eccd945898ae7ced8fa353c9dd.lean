import Mathlib

theorem algebra_96384 {m b : ℝ} (hb : b > 0)
    (h1 : 2 * (4 * m + 3 * b) = 2 * m + 16 * b) :
    m / b = 5 / 3 := by

  have eq1 : 6 * m = 10 * b := by
    linarith

  have eq2 : m = 5 / 3 * b := by
    linarith

  have eq3 : m / b = 5 / 3 := by
    have hb' : b > 0 := hb
    have h2 : m = 5 / 3 * b := eq2
    field_simp [hb']
    linarith

  exact eq3