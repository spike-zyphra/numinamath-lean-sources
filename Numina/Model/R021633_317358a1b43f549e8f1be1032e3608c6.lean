import Mathlib

theorem algebra_187647 (x : ℝ) : x * Real.log ((5 ^ (2 * x - 8)) ^ ((1 : ℝ) / 5)) - Real.log 25 = 0 ↔ x = 5 ∨ x = -1 := by
  constructor
  · -- Assume x * Real.log ((5 ^ (2 * x - 8)) ^ ((1 : ℝ) / 5)) - Real.log 25 = 0, prove x = 5 ∨ x = -1
    intro h
    have h1 : x * Real.log ((5 ^ (2 * x - 8)) ^ ((1 : ℝ) / 5)) = Real.log 25 := by linarith
    have h2 : Real.log ((5 ^ (2 * x - 8)) ^ ((1 : ℝ) / 5)) = (1 / 5) * (2 * x - 8) * Real.log 5 := by
      have h3 : Real.log ((5 ^ (2 * x - 8)) ^ ((1 : ℝ) / 5)) = ((1 : ℝ) / 5) * Real.log (5 ^ (2 * x - 8)) := by
        rw [Real.log_rpow]
        positivity
      have h4 : Real.log (5 ^ (2 * x - 8)) = (2 * x - 8) * Real.log 5 := by
        rw [Real.log_rpow]
        all_goals norm_num
      rw [h4] at h3
      linarith
    have h3 : Real.log 25 = 2 * Real.log 5 := by
      calc
        Real.log 25 = Real.log (5 ^ 2 : ℝ) := by norm_num
        _ = 2 * Real.log (5 : ℝ) := by simp [Real.log_pow]
    rw [h2] at h1
    rw [h3] at h1
    have h4 : Real.log 5 ≠ 0 := by
      positivity
    have h5 : Real.log 5 * (x * ((1 / 5) * (2 * x - 8)) - 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h5) with
    | inl h6 =>
      exfalso
      apply h4
      linarith
    | inr h7 =>
      have h6 : 2 * x ^ 2 - 8 * x - 10 = 0 := by
        nlinarith
      have h7 : (x - 5) * (x + 1) = 0 := by
        linarith [h6]
      cases (mul_eq_zero.mp h7) with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
  · -- Assume x = 5 ∨ x = -1, prove x * Real.log ((5 ^ (2 * x - 8)) ^ ((1 : ℝ) / 5)) - Real.log 25 = 0
    rintro (h | h)
    · -- x = 5
      rw [show x = (5 : ℝ) by linarith]
      have h1 : Real.log ((5 ^ (2 * (5 : ℝ) - 8)) ^ ((1 : ℝ) / 5)) = (1 / 5 : ℝ) * Real.log 25 := by
        have h2 : (5 ^ (2 * (5 : ℝ) - 8) : ℝ) = (25 : ℝ) := by
          norm_num
        rw [h2]
        have h3 : Real.log ((25 : ℝ) ^ ((1 : ℝ) / 5)) = (1 / 5 : ℝ) * Real.log 25 := by
          rw [Real.log_rpow]
          all_goals norm_num
        linarith [h3]
      nlinarith [h1, show Real.log 25 = 2 * Real.log 5 from by
        calc
          Real.log 25 = Real.log (5 ^ 2 : ℝ) := by norm_num
          _ = 2 * Real.log (5 : ℝ) := by simp [Real.log_pow]
      ]
    · -- x = -1
      rw [show x = (-1 : ℝ) by linarith]
      have h1 : Real.log ((5 ^ (2 * (-1 : ℝ) - 8)) ^ ((1 : ℝ) / 5)) = -2 * Real.log 5 := by
        have h2 : Real.log ((5 ^ (2 * (-1 : ℝ) - 8)) ^ ((1 : ℝ) / 5)) = ((1 : ℝ) / 5) * Real.log (5 ^ (2 * (-1 : ℝ) - 8)) := by
          rw [Real.log_rpow]
          positivity
        have h3 : Real.log (5 ^ (2 * (-1 : ℝ) - 8)) = (2 * (-1 : ℝ) - 8) * Real.log 5 := by
          rw [Real.log_rpow]
          all_goals norm_num
        rw [h3] at h2
        linarith
      have h3 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
        calc
          Real.log (25 : ℝ) = Real.log (5 ^ 2 : ℝ) := by norm_num
          _ = 2 * Real.log (5 : ℝ) := by simp [Real.log_pow]
      nlinarith [h1, h3]