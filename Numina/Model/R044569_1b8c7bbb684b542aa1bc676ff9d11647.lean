import Mathlib

theorem Algebra_a4 {a b c d : ℝ} (hdpos : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (h : a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 := by

  have h1 : (a ^ a * b ^ b * c ^ c * d ^ d) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    have h4 : 0 ≤ d := by linarith
    have h5 : 0 ≤ c := by linarith
    have h6 : 0 ≤ b := by linarith
    have h7 : 0 ≤ a := by linarith
    have h8 : a ^ a * b ^ b * c ^ c * d ^ d ≤ a * a + b * b + c * c + d * d := by
      apply Real.geom_mean_le_arith_mean4_weighted
      all_goals
        try {
          have ha : a ≥ 0 := by linarith
          have hb : b ≥ 0 := by linarith
          have hc : c ≥ 0 := by linarith
          have hd : d ≥ 0 := by linarith
          try nlinarith
        }
        try linarith
        try positivity

    nlinarith

  have h33 : (a + 2 * b + 3 * c + 4 * d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) < 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      mul_nonneg (show (0 : ℝ) ≤ b - c by nlinarith) (show (0 : ℝ) ≤ c - d by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ a - b by nlinarith) (show (0 : ℝ) ≤ b - c by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ a - b by nlinarith) (show (0 : ℝ) ≤ c - d by nlinarith),
      mul_pos (show 0 < d by linarith) (show 0 < c by nlinarith),
      mul_pos (show 0 < d by linarith) (show 0 < b by nlinarith),
      mul_pos (show 0 < d by linarith) (show 0 < a by nlinarith)]

  have h39 : (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) < 1 := by
    have h39 : (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) ≤ (a + 2 * b + 3 * c + 4 * d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      linarith [h1]
      all_goals
        nlinarith
    nlinarith [h33]

  linarith