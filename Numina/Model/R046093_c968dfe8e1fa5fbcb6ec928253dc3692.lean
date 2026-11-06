import Mathlib

theorem inequalities_27911 (a b c : ℝ) (ha : a ∈ Set.Icc (1 / 2) 1) (hb : b ∈ Set.Icc (1 / 2) 1)
    (hc : c ∈ Set.Icc (1 / 2) 1) :
    2 ≤ (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ∧
    (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≤ 3 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  constructor
  · -- Prove the lower bound: 2 ≤ (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b)
    have h1 : 0 < 1 + c := by nlinarith
    have h2 : 0 < 1 + a := by nlinarith
    have h3 : 0 < 1 + b := by nlinarith
    have h4 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≥ 2 := by
      have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 2 ≥ 0 := by
        have pos1 : 0 < (1 + c) * (1 + a) * (1 + b) := by positivity
        have h6 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 2 =
            ((a + b) * (1 + a) * (1 + b) + (b + c) * (1 + c) * (1 + b) + (c + a) * (1 + c) * (1 + a) - 2 * (1 + c) * (1 + a) * (1 + b)) / ((1 + c) * (1 + a) * (1 + b)) := by
          field_simp
          ring
        rw [h6] at *
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ b - 1 / 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b - 1 / 2 by linarith) (show (0 : ℝ) ≤ c - 1 / 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c - 1 / 2 by linarith) (show (0 : ℝ) ≤ a - 1 / 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - c by linarith) (show (0 : ℝ) ≤ 1 - a by linarith)]
        positivity
      linarith
    linarith
  · -- Prove the upper bound: (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≤ 3
    have h1 : 0 < 1 + c := by nlinarith
    have h2 : 0 < 1 + a := by nlinarith
    have h3 : 0 < 1 + b := by nlinarith
    have h4 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≤ 3 := by
      have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 3 ≤ 0 := by
        have pos1 : 0 < (1 + c) * (1 + a) * (1 + b) := by positivity
        have h6 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 3 =
            ((a + b) * (1 + a) * (1 + b) + (b + c) * (1 + c) * (1 + b) + (c + a) * (1 + c) * (1 + a) - 3 * (1 + c) * (1 + a) * (1 + b)) / ((1 + c) * (1 + a) * (1 + b)) := by
          field_simp
          ring
        rw [h6] at *
        apply div_nonpos_of_nonpos_of_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg (show (0 : ℝ) ≤ a - 1 / 2 by linarith) (show (0 : ℝ) ≤ b - 1 / 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b - 1 / 2 by linarith) (show (0 : ℝ) ≤ c - 1 / 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c - 1 / 2 by linarith) (show (0 : ℝ) ≤ a - 1 / 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - c by linarith) (show (0 : ℝ) ≤ 1 - a by linarith)]
        positivity
      linarith
    linarith