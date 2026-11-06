import Mathlib

theorem algebra_298434 (a b c : ℝ) (h₀ : a + b + c = 2) (h₁ : a * b * c = 4) :
    abs a + abs b + abs c ≥ 6 := by
  cases' abs_cases a with ha ha
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b ≥ 0, c ≥ 0
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith)]
      · -- a ≥ 0, b ≥ 0, c < 0
        have h3 : a * b * c ≤ 0 := by
          have h4 : c < 0 := by linarith
          have h5 : a * b ≥ 0 := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
          have h6 : a * b * c ≤ 0 := by nlinarith
          linarith
        nlinarith
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b < 0, c ≥ 0
        have h3 : a * b * c ≤ 0 := by
          have h4 : b < 0 := by linarith
          have h5 : a * c ≥ 0 := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith)
          have h6 : a * b * c ≤ 0 := by nlinarith
          linarith
        nlinarith
      · -- a ≥ 0, b < 0, c < 0
        have h3 : a ≥ 0 := by linarith
        have h4 : b < 0 := by linarith
        have h5 : c < 0 := by linarith
        have h6 : abs a + abs b + abs c = a - b - c := by
          rw [abs_of_nonneg (show 0 ≤ a by linarith), abs_of_neg (show b < 0 by linarith), abs_of_neg (show c < 0 by linarith)]
          all_goals linarith
        have h7 : b + c ≤ -2 := by
          nlinarith [sq_nonneg (b - c), sq_nonneg (a - 0), sq_nonneg (b + c + 2), sq_nonneg (b * c - 4), sq_nonneg (a - 4), sq_nonneg (b - c), sq_nonneg (b + c + 2)]
        have h8 : a - b - c ≥ 6 := by
          nlinarith [sq_nonneg (b + c + 2), sq_nonneg (a - 4), sq_nonneg (b - c)]
        linarith [h6, h8]
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a < 0, b ≥ 0, c ≥ 0
        have h3 : a * b * c ≤ 0 := by
          have h4 : a < 0 := by linarith
          have h5 : b * c ≥ 0 := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)
          have h6 : a * b * c ≤ 0 := by nlinarith
          linarith
        nlinarith
      · -- a < 0, b ≥ 0, c < 0
        have h3 : a < 0 := by linarith
        have h4 : b ≥ 0 := by linarith
        have h5 : c < 0 := by linarith
        have h6 : abs a + abs b + abs c = -a + b - c := by
          rw [abs_of_neg (show a < 0 by linarith), abs_of_nonneg (show 0 ≤ b by linarith), abs_of_neg (show c < 0 by linarith)]
          all_goals linarith
        have h7 : a + c ≤ -2 := by
          nlinarith [sq_nonneg (a - c), sq_nonneg (b - 0), sq_nonneg (a + c + 2), sq_nonneg (a * c - 4), sq_nonneg (b - 4), sq_nonneg (a - c), sq_nonneg (a + c + 2)]
        have h8 : -a + b - c ≥ 6 := by
          nlinarith [sq_nonneg (a + c + 2), sq_nonneg (b - 4), sq_nonneg (a - c)]
        linarith [h6, h8]
    · cases' abs_cases c with hc hc
      · -- a < 0, b < 0, c ≥ 0
        have h3 : a < 0 := by linarith
        have h4 : b < 0 := by linarith
        have h5 : c ≥ 0 := by linarith
        have h6 : abs a + abs b + abs c = -a - b + c := by
          rw [abs_of_neg (show a < 0 by linarith), abs_of_neg (show b < 0 by linarith), abs_of_nonneg (show 0 ≤ c by linarith)]
          all_goals linarith
        have h7 : a + b ≤ -2 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (c - 0), sq_nonneg (a + b + 2), sq_nonneg (a * b - 4), sq_nonneg (c - 4), sq_nonneg (a - b), sq_nonneg (a + b + 2)]
        have h8 : -a - b + c ≥ 6 := by
          nlinarith [sq_nonneg (a + b + 2), sq_nonneg (c - 4), sq_nonneg (a - b)]
        linarith [h6, h8]
      · -- a < 0, b < 0, c < 0
        have h3 : a + b + c < 0 := by
          have ha2 : a < 0 := by linarith
          have hb2 : b < 0 := by linarith
          have hc2 : c < 0 := by linarith
          linarith
        nlinarith