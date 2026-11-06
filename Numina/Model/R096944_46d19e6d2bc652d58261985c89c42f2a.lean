import Mathlib

theorem inequalities_104454
    (a b c : ℝ)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hc : 1 ≤ c) :
    (1 + a * b * c) * (1 / a + 1 / b + 1 / c) ≥ 3 + a + b + c := by
  have h1 : a > 0 := by linarith
  have h2 : b > 0 := by linarith
  have h3 : c > 0 := by linarith
  have h4 : (1 + a * b * c) * (1 / a + 1 / b + 1 / c) - (3 + a + b + c) ≥ 0 := by
    have h5 : (1 + a * b * c) * (1 / a + 1 / b + 1 / c) - (3 + a + b + c) =
        ((1 + a * b * c) * (b * c + a * c + a * b) - (3 + a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h5]
    have h6 : (1 + a * b * c) * (b * c + a * c + a * b) ≥ (3 + a + b + c) * (a * b * c) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ b - 1 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ b - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith)]
    have h7 : ((1 + a * b * c) * (b * c + a * c + a * b) - (3 + a + b + c) * (a * b * c)) ≥ 0 := by linarith
    have h8 : a * b * c > 0 := mul_pos (mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith)) (show (0 : ℝ) < c by linarith)
    positivity
  linarith