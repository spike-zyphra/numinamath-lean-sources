import Mathlib

theorem inequalities_598645 (a b c : ℝ) (ha : 0 < c) (hc : c ≤ b) (hb : b ≤ a) :
    (a^2 - b^2)/c + (c^2 - b^2)/a + (a^2 - c^2)/b ≥ 3*a - 4*b + c := by 
  have h1 : 0 < a := by
    nlinarith
  have h2 : 0 < b := by
    nlinarith
  have h3 : 0 < a * b * c := by
    positivity
  have h4 : (a^2 - b^2)/c + (c^2 - b^2)/a + (a^2 - c^2)/b - (3*a - 4*b + c) ≥ 0 := by
    have h5 : (a^2 - b^2)/c + (c^2 - b^2)/a + (a^2 - c^2)/b - (3*a - 4*b + c) =
        (a * b * (a^2 - b^2) + b * c * (c^2 - b^2) + a * c * (a^2 - c^2) - (3*a - 4*b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (a - c)), mul_nonneg (show 0 ≤ a - b by nlinarith) (show 0 ≤ b - c by nlinarith), mul_nonneg (show 0 ≤ a - b by nlinarith) (show 0 ≤ c by linarith), mul_nonneg (show 0 ≤ b - c by nlinarith) (show 0 ≤ c by linarith), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (a * b - c * a)]
    all_goals
      positivity
  linarith