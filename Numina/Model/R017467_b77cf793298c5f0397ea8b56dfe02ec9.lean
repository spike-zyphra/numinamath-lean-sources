import Mathlib

open Real

theorem inequalities_299468 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ 1) (h2 : b ≤ 1) (h3 : c ≤ 1) :
    a / (b * c + 1) + b / (c * a + 1) + c / (a * b + 1) ≤ 2 := by
  have h4 : 0 ≤ 1 - a := by linarith
  have h5 : 0 ≤ 1 - b := by linarith
  have h6 : 0 ≤ 1 - c := by linarith
  have h7 : a / (b * c + 1) + b / (c * a + 1) + c / (a * b + 1) - 2 ≤ 0 := by
    have h8 : a / (b * c + 1) + b / (c * a + 1) + c / (a * b + 1) - 2 =
        (a * (c * a + 1) * (a * b + 1) + b * (b * c + 1) * (a * b + 1) + c * (b * c + 1) * (c * a + 1) - 2 * (b * c + 1) * (c * a + 1) * (a * b + 1)) / ((b * c + 1) * (c * a + 1) * (a * b + 1)) := by
      field_simp
      <;> ring
    rw [h8]
    have h9 : a * (c * a + 1) * (a * b + 1) + b * (b * c + 1) * (a * b + 1) + c * (b * c + 1) * (c * a + 1) - 2 * (b * c + 1) * (c * a + 1) * (a * b + 1) ≤ 0 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ 1 - a by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith)) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith)) (show (0 : ℝ) ≤ c by linarith)
        ]
    have h10 : (a * (c * a + 1) * (a * b + 1) + b * (b * c + 1) * (a * b + 1) + c * (b * c + 1) * (c * a + 1) - 2 * (b * c + 1) * (c * a + 1) * (a * b + 1)) / ((b * c + 1) * (c * a + 1) * (a * b + 1)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      positivity
    linarith
  linarith