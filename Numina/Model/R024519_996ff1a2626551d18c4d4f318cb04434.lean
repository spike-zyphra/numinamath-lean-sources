import Mathlib

open Real

theorem inequalities_254135 (x : ℝ) :
    (1 / 5 : ℝ) * 5^(2 * x) * 7^(3 * x + 2) ≤ (25 / 7) * 7^(2 * x) * 5^(3 * x) ↔ x ≤ -3 := by
  constructor
  · -- Forward implication: inequality holds → x ≤ -3
    intro h
    have h1 : (1 / 5 : ℝ) * 5^(2 * x) * 7^(3 * x + 2) ≤ (25 / 7) * 7^(2 * x) * 5^(3 * x) := h
    have h2 : (1 / 5 : ℝ) * 5^(2 * x) * 7^(3 * x + 2) > 0 := by
      positivity
    have h3 : (25 / 7 : ℝ) * 7^(2 * x) * 5^(3 * x) > 0 := by
      positivity
    have h4 : Real.log ((1 / 5 : ℝ) * 5 ^ (2 * x) * 7 ^ (3 * x + 2)) ≤ Real.log ((25 / 7 : ℝ) * 7 ^ (2 * x) * 5 ^ (3 * x)) := by
      apply Real.log_le_log
      all_goals
        try linarith [h2, h3]
        try linarith [h1, h2, h3]
    have h5 : Real.log ((1 / 5 : ℝ) * 5 ^ (2 * x) * 7 ^ (3 * x + 2)) =
        Real.log (1 / 5) + Real.log (5 ^ (2 * x)) + Real.log (7 ^ (3 * x + 2)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h6 : Real.log ((25 / 7 : ℝ) * 7 ^ (2 * x) * 5 ^ (3 * x)) =
        Real.log (25 / 7 : ℝ) + Real.log (7 ^ (2 * x)) + Real.log (5 ^ (3 * x)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    rw [h5, h6] at h4
    have h7 : Real.log (1 / 5 : ℝ) = - Real.log (5 : ℝ) := by
      simp [Real.log_div, Real.log_one]
    have h8 : Real.log (25 / 7 : ℝ) = 2 * Real.log (5 : ℝ) - Real.log (7 : ℝ) := by
      have h9 : (25 / 7 : ℝ) = (25 : ℝ) / (7 : ℝ) := by ring
      rw [h9]
      have h10 : Real.log ((25 : ℝ) / (7 : ℝ)) = Real.log (25 : ℝ) - Real.log (7 : ℝ) := by
        rw [Real.log_div (by norm_num) (by norm_num)]
      rw [h10]
      have h11 : Real.log (25 : ℝ) = 2 * Real.log (5 : ℝ) := by
        calc
          Real.log (25 : ℝ) = Real.log ((5 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log (5 : ℝ) := by simp [Real.log_pow]
      rw [h11]
    have h12 : Real.log (5 ^ (2 * x) : ℝ) = 2 * x * Real.log (5 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        norm_num
    have h13 : Real.log (7 ^ (3 * x + 2) : ℝ) = (3 * x + 2) * Real.log (7 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        try positivity
    have h14 : Real.log (7 ^ (2 * x) : ℝ) = 2 * x * Real.log (7 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        try positivity
    have h15 : Real.log (5 ^ (3 * x) : ℝ) = 3 * x * Real.log (5 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        try positivity
    rw [h7, h8, h12, h13, h14, h15] at h4
    have h73 : Real.log (7 : ℝ) > Real.log (5 : ℝ) := by
      apply Real.log_lt_log
      all_goals
        norm_num
    nlinarith [show Real.log (7 : ℝ) > Real.log (5 : ℝ) by
      apply Real.log_lt_log
      all_goals
        norm_num
    ]
  · -- Backward implication: x ≤ -3 → inequality holds
    intro h
    have h2 : (1 / 5 : ℝ) * 5^(2 * x) * 7^(3 * x + 2) > 0 := by
      positivity
    have h3 : (25 / 7 : ℝ) * 7^(2 * x) * 5^(3 * x) > 0 := by
      positivity
    have h19 : Real.log ((1 / 5 : ℝ) * 5 ^ (2 * x) * 7 ^ (3 * x + 2)) ≤ Real.log ((25 / 7 : ℝ) * 7 ^ (2 * x) * 5 ^ (3 * x)) := by
      have h5 : Real.log ((1 / 5 : ℝ) * 5 ^ (2 * x) * 7 ^ (3 * x + 2)) =
          Real.log (1 / 5 : ℝ) + Real.log (5 ^ (2 * x)) + Real.log (7 ^ (3 * x + 2)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have h6 : Real.log ((25 / 7 : ℝ) * 7 ^ (2 * x) * 5 ^ (3 * x)) =
          Real.log (25 / 7 : ℝ) + Real.log (7 ^ (2 * x)) + Real.log (5 ^ (3 * x)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      have h7 : Real.log (1 / 5 : ℝ) = - Real.log (5 : ℝ) := by
        simp [Real.log_div, Real.log_one]
      have h8 : Real.log (25 / 7 : ℝ) = 2 * Real.log (5 : ℝ) - Real.log (7 : ℝ) := by
        have h9 : (25 / 7 : ℝ) = (25 : ℝ) / (7 : ℝ) := by ring
        rw [h9]
        have h10 : Real.log ((25 : ℝ) / (7 : ℝ)) = Real.log (25 : ℝ) - Real.log (7 : ℝ) := by
          rw [Real.log_div (by norm_num) (by norm_num)]
        rw [h10]
        have h11 : Real.log (25 : ℝ) = 2 * Real.log (5 : ℝ) := by
          calc
            Real.log (25 : ℝ) = Real.log ((5 : ℝ) ^ 2) := by norm_num
            _ = 2 * Real.log (5 : ℝ) := by simp [Real.log_pow]
        rw [h11]
      have h12 : Real.log (5 ^ (2 * x) : ℝ) = 2 * x * Real.log (5 : ℝ) := by
        rw [Real.log_rpow]
        all_goals
          norm_num
      have h13 : Real.log (7 ^ (3 * x + 2) : ℝ) = (3 * x + 2) * Real.log (7 : ℝ) := by
        rw [Real.log_rpow]
        all_goals
          try positivity
      have h14 : Real.log (7 ^ (2 * x) : ℝ) = 2 * x * Real.log (7 : ℝ) := by
        rw [Real.log_rpow]
        all_goals
          try positivity
      have h15 : Real.log (5 ^ (3 * x) : ℝ) = 3 * x * Real.log (5 : ℝ) := by
        rw [Real.log_rpow]
        all_goals
          try positivity
      rw [h5, h6, h7, h8, h12, h13, h14, h15]
      have h73 : Real.log (7 : ℝ) > Real.log (5 : ℝ) := by
        apply Real.log_lt_log
        all_goals
          norm_num
      nlinarith [show Real.log (7 : ℝ) > Real.log (5 : ℝ) by
        apply Real.log_lt_log
        all_goals
          norm_num
      ]
    have h20 : (1 / 5 : ℝ) * 5^(2 * x) * 7^(3 * x + 2) ≤ (25 / 7) * 7^(2 * x) * 5^(3 * x) := by
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h19
    linarith