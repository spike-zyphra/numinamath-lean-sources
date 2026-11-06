import Mathlib


theorem algebra_106468 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a * Real.sqrt b - c = a) (h2 : b * Real.sqrt c - a = b) (h3 : c * Real.sqrt a - b = c) :
    b = 0 ∨ b = 4 := by

  have eq1 : a * (Real.sqrt b - 1) = c := by linarith
  have eq2 : b * (Real.sqrt c - 1) = a := by linarith
  have eq3 : c * (Real.sqrt a - 1) = b := by linarith

  by_cases hb0 : b = 0
  · -- $b = 0$.
    left
    exact hb0
  · -- $b \neq 0$.
    have hb_pos : 0 < b := by
      by_contra h
      push_neg at h
      have : b = 0 := by linarith
      contradiction

    have ha_pos : 0 < a := by
      by_contra h
      push_neg at h
      have ha0 : a = 0 := by linarith
      rw [ha0] at eq2
      have h4 : b * (Real.sqrt c - 1) = 0 := by linarith
      have h5 : Real.sqrt c - 1 = 0 := by
        apply (mul_left_inj' (show b ≠ 0 by linarith)).mp
        linarith
      have h6 : Real.sqrt c = 1 := by linarith
      have h7 : c = 1 := by
        calc
          c = (Real.sqrt c) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = 1 ^ 2 := by rw [h6]
          _ = (1 : ℝ) := by norm_num
      rw [ha0, h7] at eq3
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (c : ℝ) by linarith)]

    have hc_pos : 0 < c := by
      by_contra h
      push_neg at h
      have hc0 : c = 0 := by linarith
      rw [hc0] at eq3
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (c : ℝ) by linarith)]

    have h4 : b = 4 := by
      have h5 : Real.sqrt a = 2 := by
        nlinarith [sq_nonneg (Real.sqrt a - 2), sq_nonneg (Real.sqrt b - 2), sq_nonneg (Real.sqrt c - 2),
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a)]
      have ha4 : a = 4 := by
        calc
          a = (Real.sqrt a) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = (2 : ℝ) ^ 2 := by rw [h5]
          _ = (4 : ℝ) := by norm_num
      have h7 : Real.sqrt c = 2 := by
        nlinarith [sq_nonneg (Real.sqrt a - 2), sq_nonneg (Real.sqrt b - 2), sq_nonneg (Real.sqrt c - 2),
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a)]
      have hc4 : c = 4 := by
        calc
          c = (Real.sqrt c) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = (2 : ℝ) ^ 2 := by rw [h7]
          _ = (4 : ℝ) := by norm_num
      have h7 : Real.sqrt b = 2 := by
        nlinarith [sq_nonneg (Real.sqrt a - 2), sq_nonneg (Real.sqrt b - 2), sq_nonneg (Real.sqrt c - 2),
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a)]
      have hb4 : b = 4 := by
        calc
          b = (Real.sqrt b) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = (2 : ℝ) ^ 2 := by rw [h7]
          _ = (4 : ℝ) := by norm_num
      exact hb4

    right
    linarith