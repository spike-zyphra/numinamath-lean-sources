import Mathlib

theorem inequalities_134950 (a b c d : ℝ) (ha : a > b) (hb : b > c) (hc : c > d) (hd : d ≥ 0)
    (h : a + d = b + c) (x : ℝ) (hx : x > 0) : x * a + x * d ≥ x * b + x * c := by
  have h2 : a + d = b + c := h
  have h3 : x * a + x * d = x * b + x * c := by
    have h4 : x * (a + d) = x * (b + c) := by 
      rw [show a + d = b + c by linarith]
    have h5 : x * a + x * d = x * (a + d) := by
      ring
    have h6 : x * b + x * c = x * (b + c) := by
      ring
    linarith [h4, h5, h6]
  linarith [h3]
  all_goals linarith