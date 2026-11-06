import Mathlib

theorem algebra_15121 : IsGreatest {y : ℝ | ∃ x : ℝ, y = 10 ^ x - 100 ^ x} (1 / 4) := by
  constructor
  · -- Show 1/4 is in the set
    use (Real.logb 10 (1 / 2 : ℝ))
    have h1 : (10 : ℝ) ^ (Real.logb 10 (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      rw [Real.rpow_logb]
      all_goals norm_num
    have h2 : (100 : ℝ) ^ (Real.logb 10 (1 / 2 : ℝ)) = (1 / 4 : ℝ) := by
      have h3 : (100 : ℝ) ^ (Real.logb 10 (1 / 2 : ℝ)) = ((10 : ℝ) ^ (2 : ℝ)) ^ (Real.logb 10 (1 / 2 : ℝ)) := by
        norm_num
      rw [h3]
      have h4 : ((10 : ℝ) ^ (2 : ℝ)) ^ (Real.logb 10 (1 / 2 : ℝ)) = (10 : ℝ) ^ (2 * Real.logb 10 (1 / 2 : ℝ)) := by
        rw [← Real.rpow_mul]
        ring
        all_goals norm_num
      rw [h4]
      have h5 : (10 : ℝ) ^ (2 * Real.logb 10 (1 / 2 : ℝ)) = ((10 : ℝ) ^ (Real.logb 10 (1 / 2 : ℝ)) ) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring
        all_goals norm_num
      rw [h5, h1]
      all_goals norm_num
    linarith [h1, h2]
  · -- Show 1/4 is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h3 : (100 : ℝ) ^ x = (10 : ℝ) ^ (2 * x) := by
      calc
        (100 : ℝ) ^ x = ((10 : ℝ) ^ (2 : ℝ)) ^ x := by norm_num
        _ = (10 : ℝ) ^ (2 * x) := by rw [← Real.rpow_mul]; ring; all_goals norm_num
    have h4 : (10 : ℝ) ^ (2 * x) = ((10 : ℝ) ^ x) ^ 2 := by
      calc
        (10 : ℝ) ^ (2 * x) = (10 : ℝ) ^ (2 * x) := by rfl
        _ = ((10 : ℝ) ^ x) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring
          all_goals norm_num
    have h5 : (100 : ℝ) ^ x = ((10 : ℝ) ^ x) ^ 2 := by
      rw [h3, h4]
    have h6 : (10 ^ x - (100 : ℝ) ^ x) ≤ (1 / 4 : ℝ) := by
      have h7 : (100 : ℝ) ^ x = ((10 : ℝ) ^ x) ^ 2 := h5
      rw [h7]
      nlinarith [sq_nonneg ((10 : ℝ) ^ x - (1 / 2 : ℝ)), Real.rpow_nonneg (show (0 : ℝ) ≤ (10 : ℝ) by norm_num) x]
    have h7 : y = (10 ^ x - (100 : ℝ) ^ x) := by linarith [hx]
    linarith [h7, h6]