import Mathlib

theorem inequalities_219424 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c > a ∧ a > b) : a / (c - a) > b / (c - b) := by
  have h1 : c > a := h.1
  have h2 : a > b := h.2
  have pos1 : c - a > 0 := by linarith
  have pos2 : c - b > 0 := by linarith
  have h3 : a * (c - b) - b * (c - a) > 0 := by
    have h4 : c * (a - b) > 0 := by
      apply mul_pos
      linarith
      linarith
    nlinarith
  have h4 : a * (c - b) > b * (c - a) := by linarith [h3]
  apply (div_lt_div_iff (by positivity) (by positivity)).mpr
  nlinarith