import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_245851 {f : ℝ → ℝ} (hf : f = λ x => abs (log (x + 1))) :
    ∃ a b, a < b ∧ f a = f (- (b + 1) / (b + 2)) ∧ f (10 * a + 6 * b + 21) = 4 * log 2 := by

  use -2 / 5, -1 / 3
  constructor
  · -- Show $a < b$ i.e., $-2/5 < -1/3$
    norm_num
  constructor
  · -- Show $f(-2/5) = f(-(b + 1) / (b + 2))$
    rw [hf]
    have h1 : abs (log (-2 / 5 + 1)) = abs (log (- ( -1 / 3 + 1 ) / ( -1 / 3 + 2 ) + 1 )) := by
      have h5 : log (-2 / 5 + 1) = log (3 / 5) := by
        norm_num
      have h6 : log (- ( -1 / 3 + 1 ) / ( -1 / 3 + 2 ) + 1 ) = log (3 / 5) := by
        have h7 : (- ( -1 / 3 + 1 ) / ( -1 / 3 + 2 ) + 1 : ℝ) = (3 / 5 : ℝ) := by 
          norm_num
        rw [h7]
      rw [h5, h6]
      all_goals norm_num
    simpa using h1
  · -- Show $f(10a+6b+21) = 4\cdot \log 2$
    rw [hf]
    have h1 : abs (log (10 * (-2 / 5 : ℝ) + 6 * (-1 / 3) + 21 + 1)) = 4 * log 2 := by
      have h10 : (10 * (-2 / 5 : ℝ) + 6 * (-1 / 3) + 21 + 1 : ℝ) = (16 : ℝ) := by norm_num
      rw [h10]
      have h6 : log (16 : ℝ) = 4 * log 2 := by
        calc
          log (16 : ℝ) = log ((2: ℝ) ^ 4) := by norm_num
          _ = 4 * log (2: ℝ) := by simp [log_pow]
      have h2_pos : 0 ≤ log 2 := by
        have h3_pos : (2: ℝ) > 0 := by norm_num
        have h4_pos : log (2: ℝ) > 0 := by
          apply log_pos
          all_goals linarith
        linarith
      have h5_pos : 0 ≤ (4 * log 2 : ℝ) := by linarith
      have hlog_pos : log 16 = (4 * log 2 : ℝ) := by
        have h6 : log (16 : ℝ) = 4 * log 2 := by
          calc
            log (16 : ℝ) = log ((2: ℝ) ^ 4) := by norm_num
            _ = 4 * log (2: ℝ) := by simp [log_pow]
        norm_num at h6 ⊢
        all_goals linarith
      rw [show log (16 : ℝ) = 4 * log 2 by linarith [h6]]
      all_goals
        norm_num [abs_of_nonneg, h2_pos]
        <;> norm_num [h6]
        <;> norm_num
    simpa using h1
    all_goals norm_num
    <;> norm_num
    <;> norm_num
    <;> norm_num