import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_309753 {x : ℝ} :
  abs (x + 7) - abs (3 * x - 4) + sqrt (3 - 2 * sqrt 2) > 0 ↔
  (2 + sqrt 2) / (-4) < x ∧ x < (10 + sqrt 2) / 2 := by
  have h1 : sqrt (3 - 2 * sqrt 2) = Real.sqrt 2 - 1 := by
    have h2 : (Real.sqrt 2 - 1 : ℝ) ^ 2 = 3 - 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
      rw [← h2]
      field_simp [Real.sqrt_nonneg (Real.sqrt 2 - 1), Real.sqrt_nonneg (3 - 2 * Real.sqrt 2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (Real.sqrt 2 - 1)]
      all_goals nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 - 2 * Real.sqrt 2), Real.sqrt_nonneg (Real.sqrt 2 - 1)]
    exact h3
  rw [h1]
  constructor
  · -- Forward direction: if $|x+7|-|3x-4| + (\sqrt{2} - 1) >0$, then $-\frac{1}{4}(2+\sqrt{2}) < x < \frac{1}{2}(10+\sqrt{2})$
    intro h
    by_cases h2 : x < -7
    · -- x < -7
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
      exfalso
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    by_cases h3 : x ≤ 4 / 3
    · -- -7 ≤ x ≤ 4/3
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
      constructor
      · nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- x > 4/3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      constructor
      · nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Backward direction: if $-\frac{1}{4}(2+\sqrt{2}) < x < \frac{1}{2}(10+\sqrt{2})$, then $|x+7|-|3x-4| + (\sqrt{2} - 1) >0$
    rintro ⟨h1, h2⟩
    by_cases h2 : x < -7
    · -- x < -7
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    by_cases h3 : x ≤ 4 / 3
    · -- -7 ≤ x ≤ 4/3
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- x > 4/3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]