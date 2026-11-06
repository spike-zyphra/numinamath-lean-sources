import Mathlib

theorem algebra_9448 (x : ℝ) : 9 ^ x + 3 ^ x - 6 = (0 : ℝ) ↔ x = Real.logb 3 2 := by
  constructor
  · -- Assume 9 ^ x + 3 ^ x - 6 = (0 : ℝ) (→)
    intro h_eq
    have h1 : (9 : ℝ) ^ x = (3 : ℝ) ^ (2 * x) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h2 : ((3 : ℝ) ^ (2 * x)) = ((3 : ℝ) ^ x) ^ 2 := by
      calc
        (3 : ℝ) ^ (2 * x) = (3 ^ (x * 2 : ℝ)) := by ring_nf
        _ = (3 ^ (x : ℝ)) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring_nf; all_goals norm_num
    rw [h1, h2] at h_eq
    have h3 : ((3 : ℝ) ^ x) ^ 2 + (3 : ℝ) ^ x - 6 = (0 : ℝ) := by
      nlinarith
    have h4 : ((3 : ℝ) ^ x + 3) * ((3 : ℝ) ^ x - 2) = (0 : ℝ) := by
      nlinarith [h3]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Assume h5 : (3 : ℝ) ^ x + 3 = 0
      have h7 : (3 : ℝ) ^ x = (-3 : ℝ) := by linarith
      have h8 : (3 : ℝ) ^ x > (0 : ℝ) := by positivity
      linarith
    · -- Assume h6 : (3 : ℝ) ^ x - 2 = 0
      have h9 : (3 : ℝ) ^ x = (2 : ℝ) := by linarith
      have h10 : x = Real.logb 3 (2 : ℝ) := by
        rw [← h9]
        field_simp
      exact_mod_cast h10
  · -- Assume x = Real.logb 3 2 (←)
    intro h_eq
    have h11 : (3 : ℝ) ^ x = (2 : ℝ) := by
      rw [show x = Real.logb 3 2 by linarith [h_eq]]
      field_simp
    have h15 : (9 : ℝ) ^ x = (3 : ℝ) ^ (2 * x) := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h16 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by
      have eq1 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by
        have eq2 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        exact_mod_cast eq2
      exact_mod_cast eq1
    have h17 : (9 : ℝ) ^ x + (3 : ℝ) ^ x - 6 = (0 : ℝ) := by
      have eq1 : (9 : ℝ) ^ x = ((3 : ℝ) ^ x) ^ 2 := by
        linarith [h15, h16]
      rw [eq1, h11]
      all_goals norm_num
    linarith [h17]