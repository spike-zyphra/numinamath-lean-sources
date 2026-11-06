import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_105771 {g : ℝ → ℝ} (hg : g = λ x => log (2^x + 1)) :
    g (-4) - g (-3) + g (-2) - g (-1) + g 1 - g 2 + g 3 - g 4 = -2 * log 2 := by
  simp [hg]
  have h1 : log (17 / (16 : ℝ)) = log (17 : ℝ) - log (16 : ℝ) := by
    rw [log_div (by norm_num) (by norm_num)]
  have h2 : log (9 / (8 : ℝ)) = log (9 : ℝ) - log (8 : ℝ) := by
    rw [log_div (by norm_num) (by norm_num)]
  have h3 : log (5 / (4 : ℝ)) = log (5 : ℝ) - log (4 : ℝ) := by
    rw [log_div (by norm_num) (by norm_num)]
  have h4 : log (3 / (2 : ℝ)) = log (3 : ℝ) - log (2 : ℝ) := by
    rw [log_div (by norm_num) (by norm_num)]
  have h5 : log (16 : ℝ) = 4 * log 2 := by
    calc
      log (16 : ℝ) = log ((2 : ℝ) ^ 4) := by norm_num
      _ = 4 * log (2 : ℝ) := by simp [log_pow]
      _ = 4 * log 2 := by ring
  have h6 : log (8 : ℝ) = 3 * log 2 := by
    calc
      log (8 : ℝ) = log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * log (2 : ℝ) := by simp [log_pow]
      _ = 3 * log 2 := by ring
  have h7 : log (4 : ℝ) = 2 * log 2 := by
    calc
      log (4 : ℝ) = log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * log (2 : ℝ) := by simp [log_pow]
      _ = 2 * log 2 := by ring
  have h8 : log (9 : ℝ) = 2 * log 3 := by
    calc
      log (9 : ℝ) = log ((3 : ℝ) ^ 2) := by norm_num
      _ = 2 * log (3 : ℝ) := by simp [log_pow]
      _ = 2 * log 3 := by ring
  have h9 : log (17 / (16 : ℝ)) - log (9 / (8 : ℝ)) + log (5 / (4 : ℝ)) - log (3 / (2 : ℝ)) + log (3 : ℝ) - log (5 : ℝ) + log (9 : ℝ) - log (17 : ℝ) = -2 * log 2 := by
    have h17 : log (17 / (16 : ℝ)) = log (17 : ℝ) - 4 * log 2 := by
      rw [log_div (by norm_num) (by norm_num)]
      rw [h5]
      all_goals norm_num
    have h18 : log (9 / (8 : ℝ)) = 2 * log 3 - 3 * log 2 := by
      have h2 : log (9 / (8 : ℝ)) = log (9 : ℝ) - log (8 : ℝ) := by
        rw [log_div (by norm_num) (by norm_num)]
      rw [h2]
      rw [h6, h8]
      all_goals norm_num
    have h19 : log (5 / (4 : ℝ)) = log (5 : ℝ) - 2 * log 2 := by
      have h3 : log (5 / (4 : ℝ)) = log (5 : ℝ) - log (4 : ℝ) := by
        rw [log_div (by norm_num) (by norm_num)]
      rw [h3]
      rw [h7]
      all_goals norm_num
    have h20 : log (3 / (2 : ℝ)) = log (3 : ℝ) - log (2 : ℝ) := by
      rw [log_div (by norm_num) (by norm_num)]
    rw [h17, h18, h19, h20]
    all_goals linarith
  norm_num at h9 ⊢
  <;> linarith [h9]