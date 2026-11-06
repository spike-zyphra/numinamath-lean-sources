import Mathlib

open Real Set
open scoped BigOperators

/- 7. The solution set of the inequality $\left|\frac{1}{\log _{\frac{1}{3}} x+1}\right|>\frac{1}{3}$ is ( ).
(A) $\left(\frac{1}{9}, 81\right)$
(B) $\left(\frac{1}{3}, 3\right) \cup(3,27)$
(C) $\left(\frac{1}{3}, 27\right)$
(D) $\left(\frac{1}{9}, 3\right) \cup(3,81)$ -/
theorem inequalities_319497 {x : ℝ} (hx : 0 < x) :
    abs (1 / (logb (1 / 3) x + 1)) > 1 / 3 ↔
    (1 / 9 < x ∧ x < 3 ∨ 3 < x ∧ x < 81) := by
  -- Convert logb(1/3) x to -logb(3) x for easier manipulation
  have h1 : logb (1 / 3) x = -logb 3 x := by
    rw [logb]
    simp [logb]
    all_goals linarith
  rw [h1]
  constructor
  · -- Forward direction: Assume |1/(-logb 3 x + 1)| > 1/3, prove x ∈ (1/9, 3) ∪ (3, 81)
    intro h
    -- Prove that -logb 3 x + 1 ≠ 0 (which means x ≠ 3)
    have h2 : -logb 3 x + 1 ≠ 0 := by
      by_contra h3
      have h4 : logb 3 x = 1 := by linarith
      have h5 : x = 3 := by
        rw [logb_eq_iff_rpow_eq] at h4
        · linarith
        all_goals linarith
      rw [h5] at h
      norm_num [logb] at h
    -- Prove that |-logb 3 x + 1| < 3 using contradiction
    have h4 : abs (-logb 3 x + 1) < 3 := by
      by_contra h5
      have h7 : abs (1 / (-logb 3 x + 1)) ≤ 1 / 3 := by
        have h8 : abs (1 / (-logb 3 x + 1)) = 1 / abs (-logb 3 x + 1) := by
          field_simp [abs_div, h2]
        rw [h8]
        have h10 : (1 : ℝ) / abs (-logb 3 x + 1) ≤ 1 / 3 := by
          apply one_div_le_one_div_of_le
          all_goals linarith
        linarith
      linarith
    -- Establish bounds on logb 3 x: -2 < logb 3 x < 4
    have h5 : -2 < logb 3 x := by
      cases' abs_cases (-logb 3 x + 1) with h6 h6
      · -- Case when -logb 3 x + 1 ≥ 0
        linarith
      · -- Case when -logb 3 x + 1 < 0
        linarith
    have h6 : logb 3 x < 4 := by
      cases' abs_cases (-logb 3 x + 1) with h7 h7
      · -- Case when -logb 3 x + 1 ≥ 0
        linarith
      · -- Case when -logb 3 x + 1 < 0
        linarith
    -- Prove the lower bound: 1/9 < x
    have h7 : 1 / 9 < x := by
      have h8 : logb 3 x > -2 := by linarith
      have h9 : logb 3 (1 / 9 : ℝ) = -2 := by
        rw [show (1 / 9 : ℝ) = (3 ^ (-2 : ℝ)) by norm_num]
        simp [logb_rpow]
      have h10 : x > (1 / 9 : ℝ) := by
        have h11 : logb 3 x > logb 3 (1 / 9 : ℝ) := by linarith [h8, h9]
        have h13 : x > (1 / 9 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mp h11
        linarith
      linarith
    -- Prove the upper bound: x < 81
    have h8 : x < (81 : ℝ) := by
      have h9 : logb 3 x < (4 : ℝ) := by linarith
      have h10 : logb 3 (81 : ℝ) = (4 : ℝ) := by
        rw [show (81 : ℝ) = (3 ^ (4 : ℝ)) by norm_num]
        simp [logb_rpow]
      have h11 : x < (81 : ℝ) := by
        have h12 : logb 3 x < logb 3 (81 : ℝ) := by linarith [h9, h10]
        have h13 : x < (81 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mp h12
        linarith
      linarith
    -- Prove that x ≠ 3
    have h9 : x ≠ 3 := by
      by_contra h10
      have h11 : -logb 3 x + 1 = 0 := by
        rw [h10]
        norm_num [logb]
      contradiction
    -- Case analysis: either x < 3 or x > 3
    by_cases h10 : x < 3
    · -- If x < 3, then we have 1/9 < x < 3
      left
      constructor
      · linarith
      · -- Show x < 3
        linarith
    · -- If x ≥ 3, then x > 3 (by x ≠ 3)
      have h11 : x > 3 := by
        by_contra h12
        push_neg at h12
        have h13 : x = 3 := by linarith
        contradiction
      right
      constructor
      · -- Show 3 < x
        linarith
      · -- Show x < 81
        linarith
  · -- Backward direction: Assume x ∈ (1/9, 3) ∪ (3, 81), prove |1/(-logb 3 x + 1)| > 1/3
    rintro (h | h)
    · -- Case 1: 1/9 < x < 3
      -- Establish bounds on logb 3 x: -2 < logb 3 x < 1
      have h3 : logb 3 x > -2 := by
        have h4 : logb 3 (1 / 9 : ℝ) = -2 := by
          rw [show (1 / 9 : ℝ) = (3 ^ (-2 : ℝ)) by norm_num]
          simp [logb_rpow]
        have h5 : logb 3 x > logb 3 (1 / 9 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mpr
          all_goals linarith
        linarith [h4, h5]
      have h4 : logb 3 x < (1 : ℝ) := by
        have h5 : logb 3 (3 : ℝ) = (1 : ℝ) := by
          rw [logb_self_eq_one]
          all_goals linarith
        have h6 : logb 3 x < logb 3 (3 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mpr
          all_goals linarith
        linarith [h5, h6]
      -- Prove that |1/(-logb 3 x + 1)| > 1/3 for this case
      have h5 : abs (1 / (-logb 3 x + 1)) > 1 / 3 := by
        have h6 : -logb 3 x + 1 > 0 := by linarith
        have h7 : abs (-logb 3 x + 1) = -logb 3 x + 1 := by
          rw [abs_of_pos]
          linarith
        have h8 : abs (1 / (-logb 3 x + 1)) = 1 / abs (-logb 3 x + 1) := by
          field_simp [abs_div, h6]
        rw [h8, h7]
        have h10 : (1 : ℝ) / (-logb 3 x + 1) > 1 / 3 := by
          apply one_div_lt_one_div_of_lt
          all_goals linarith
        linarith
      simpa using h5
    · -- Case 2: 3 < x < 81
      -- Establish bounds on logb 3 x: 1 < logb 3 x < 4
      have h3 : logb 3 x > (1 : ℝ) := by
        have h4 : logb 3 (3 : ℝ) = (1 : ℝ) := by
          rw [logb_self_eq_one]
          all_goals linarith
        have h5 : logb 3 x > logb 3 (3 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mpr
          all_goals linarith
        linarith [h4, h5]
      have h4 : logb 3 x < (4 : ℝ) := by
        have h5 : logb 3 (81 : ℝ) = (4 : ℝ) := by
          rw [show (81 : ℝ) = (3 ^ (4 : ℝ)) by norm_num]
          simp [logb_rpow]
        have h6 : logb 3 x < logb 3 (81 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mpr
          all_goals linarith
        linarith [h5, h6]
      -- Prove that |1/(-logb 3 x + 1)| > 1/3 for this case
      have h5 : abs (1 / (-logb 3 x + 1)) > 1 / 3 := by
        have h7 : abs (-logb 3 x + 1) = logb 3 x - 1 := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h8 : abs (1 / (-logb 3 x + 1)) = 1 / abs (-logb 3 x + 1) := by
          field_simp [abs_div, show (-logb 3 x + 1) ≠ 0 by linarith]
        rw [h8, h7]
        have h11 : (1 : ℝ) / (logb 3 x - 1) > 1 / 3 := by
          apply one_div_lt_one_div_of_lt
          all_goals linarith
        linarith
      simpa using h5
