import Mathlib

theorem inequalities_85952 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 3) :
    abs a + abs b + abs c - a * b * c ≤ 4 := by 
  cases' abs_cases a with ha ha
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b ≥ 0, c ≥ 0
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith)]
      · -- a ≥ 0, b ≥ 0, c < 0
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c + 1),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ -c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ -c by linarith)]
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b < 0, c ≥ 0
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (c - 1),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ -b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -b by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith)]
      · -- a ≥ 0, b < 0, c < 0
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (c + 1),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ -b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -b by linarith) (show (0 : ℝ) ≤ -c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ -c by linarith)]
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a < 0, b ≥ 0, c ≥ 0
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ c by linarith)]
      · -- a < 0, b ≥ 0, c < 0
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (c + 1),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ -c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -c by linarith)]
    · cases' abs_cases c with hc hc
      · -- a < 0, b < 0, c ≥ 0
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c - 1),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -b by linarith) (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ c by linarith)]
      · -- a < 0, b < 0, c < 0
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -b by linarith) (show (0 : ℝ) ≤ -c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -c by linarith)]