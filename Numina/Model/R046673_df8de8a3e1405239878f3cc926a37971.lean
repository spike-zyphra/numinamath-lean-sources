import Mathlib

theorem inequalities_597805 (a b c d : ℝ) (ha : 0 < d) (hd : d ≤ c) (hc : c ≤ b) (hb : b ≤ a) :
    ((1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a))) ≥ (3 / 2)^4 := by

  have ha1 : 0 < a := by linarith
  have ha2 : 0 < b := by linarith
  have ha3 : 0 < c := by linarith

  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + d := by linarith
  have h4 : 0 < d + a := by linarith

  have h5 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) =
      ((a + b + c) * (b + c + d) * (c + d + a) * (d + a + b)) / ((a + b) * (b + c) * (c + d) * (d + a)) := by
    field_simp
    all_goals ring

  rw [h5] at *

  have h7 : ((a + b + c) * (b + c + d) * (c + d + a) * (d + a + b)) ≥ (81 / 16) * ((a + b) * (b + c) * (c + d) * (d + a)) := by
    have h8 : 0 ≤ (a - b) * (b - c) * (c - d) := by
      have h9 : 0 ≤ a - b := by linarith
      have h10 : 0 ≤ b - c := by linarith
      have h11 : 0 ≤ c - d := by linarith
      positivity

    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
        sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c),
        mul_nonneg (show (0 : ℝ) ≤ a - b by linarith) (show (0 : ℝ) ≤ b - c by linarith),
        mul_nonneg (show (0 : ℝ) ≤ b - c by linarith) (show (0 : ℝ) ≤ c - d by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a - b by linarith) (show (0 : ℝ) ≤ c - d by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ d by linarith),
        mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
        mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ d by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
        mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ d by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a - b by linarith) (show (0 : ℝ) ≤ d by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a - c by linarith) (show (0 : ℝ) ≤ c by linarith),
        mul_nonneg (show (0 : ℝ) ≤ b - c by linarith) (show (0 : ℝ) ≤ c by linarith),
        mul_nonneg (show (0 : ℝ) ≤ a - b by linarith) (show (0 : ℝ) ≤ c - d by linarith)]

  have h6 : ((a + b + c) * (b + c + d) * (c + d + a) * (d + a + b)) / ((a + b) * (b + c) * (c + d) * (d + a)) ≥ (3 / 2)^4 := by
    have h13 : ((a + b + c) * (b + c + d) * (c + d + a) * (d + a + b)) ≥ (81 / 16 : ℝ) * ((a + b) * (b + c) * (c + d) * (d + a)) := by
      linarith [h7]

    have h13' : ((a + b + c) * (b + c + d) * (c + d + a) * (d + a + b)) / ((a + b) * (b + c) * (c + d) * (d + a)) ≥ (81 / 16 : ℝ) := by
      have h14 : (a + b) * (b + c) * (c + d) * (d + a) > 0 := by positivity
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith

    have h15 : (81 / 16 : ℝ) = (3 / 2)^4 := by norm_num
    linarith [h15, h13']

  exact h6