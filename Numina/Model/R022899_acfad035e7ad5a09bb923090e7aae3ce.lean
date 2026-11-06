import Mathlib

theorem algebra_190044 (x : ℝ) : (5 : ℝ)^(2 * x + 1) > 5^x + 4 ↔ x > 0 := by
  constructor
  · -- Assume (5 : ℝ)^(2 * x + 1) > 5^x + 4, prove x > 0
    intro h
    have h1 : (5 : ℝ) ^ (2 * x + 1) = 5 * ((5 : ℝ) ^ x) ^ 2 := by
      calc
        (5 : ℝ) ^ (2 * x + 1) = (5 : ℝ) ^ (2 * x) * (5 : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
        _ = (5 : ℝ) ^ (2 * x) * 5 := by norm_num
        _ = ((5 : ℝ) ^ x) ^ 2 * 5 := by
          calc
            (5 : ℝ) ^ (2 * x) * 5 = ((5 : ℝ) ^ (2 * x)) * 5 := by ring
            _ = ((5 : ℝ) ^ x) ^ 2 * 5 := by
              calc
                ((5 : ℝ) ^ (2 * x)) * 5 = ((5 : ℝ) ^ (x * 2)) * 5 := by ring_nf
                _ = ( ( (5 : ℝ) ^ x ) ^ 2) * 5 := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf
                  all_goals linarith
                _ = ((5 : ℝ) ^ x) ^ 2 * 5 := by ring
        _ = 5 * ((5 : ℝ) ^ x) ^ 2 := by ring
    rw [h1] at h
    have h2 : 5 * ((5 : ℝ) ^ x) ^ 2 > (5 : ℝ) ^ x + 4 := by linarith
    have h3 : (5 : ℝ) ^ x > 1 := by
      nlinarith [show (5 : ℝ) ^ x > 0 by positivity, sq_nonneg (( (5 : ℝ) ^ x ) - 1 ) ]
    have h4 : x > 0 := by
      by_contra h4
      push_neg at h4
      have h5 : (5 : ℝ) ^ x ≤ (1 : ℝ) := by
        have h6 : (5 : ℝ) ^ (x) ≤ (5 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        have h7 : (5 : ℝ) ^ (0 : ℝ) = 1 := by
          simp
        linarith [h7]
      linarith [h3, h5]
    exact h4
  · -- Assume x > 0, prove (5 : ℝ)^(2 * x + 1) > 5^x + 4
    intro h
    have h1 : (5 : ℝ) ^ (2 * x + 1) = 5 * ((5 : ℝ) ^ x) ^ 2 := by
      calc
        (5 : ℝ) ^ (2 * x + 1) = (5 : ℝ) ^ (2 * x) * (5 : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
        _ = (5 : ℝ) ^ (2 * x) * 5 := by norm_num
        _ = ((5 : ℝ) ^ x) ^ 2 * 5 := by
          calc
            (5 : ℝ) ^ (2 * x) * 5 = ((5 : ℝ) ^ (2 * x)) * 5 := by ring
            _ = ((5 : ℝ) ^ x) ^ 2 * 5 := by
              calc
                ((5 : ℝ) ^ (2 * x)) * 5 = ((5 : ℝ) ^ (x * 2)) * 5 := by ring_nf
                _ = ( ( (5 : ℝ) ^ x ) ^ 2) * 5 := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf
                  all_goals linarith
                _ = ((5 : ℝ) ^ x) ^ 2 * 5 := by ring
        _ = 5 * ((5 : ℝ) ^ x) ^ 2 := by ring
    rw [h1]
    have h3 : (5 : ℝ) ^ x > 1 := by
      have h4 : (5 : ℝ) ^ x > (5 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      have h5 : (5 : ℝ) ^ (0 : ℝ) = 1 := by
        simp
      linarith [h4, h5]
    nlinarith [sq_pos_of_pos (show (5 : ℝ) ^ x > 0 by positivity), sq_pos_of_pos (show (5 : ℝ) > 0 by norm_num), sq_nonneg (( (5 : ℝ) ^ x ) - 1 ) ]