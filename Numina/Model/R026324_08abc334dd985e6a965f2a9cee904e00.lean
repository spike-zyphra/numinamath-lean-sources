import Mathlib

open Real

theorem inequalities_322302 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b ≤ c + 1) (h2 : b + c ≤ a + 1) (h3 : c + a ≤ b + 1) :
    (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c + 1) ≤ 3 / 2 := by

  have h4 : 0 < a * b * c + 1 := by
    have h5 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    linarith

  have h5 : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 3 * (a * b * c + 1) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
      mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
      mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith), 
      mul_nonneg (show 0 ≤ 1 - a by nlinarith) (show 0 ≤ 1 - b by nlinarith), 
      mul_nonneg (show 0 ≤ 1 - b by nlinarith) (show 0 ≤ 1 - c by nlinarith), 
      mul_nonneg (show 0 ≤ 1 - c by nlinarith) (show 0 ≤ 1 - a by nlinarith)]

  have h6 : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c + 1) ≤ 3 / 2 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith

  exact h6