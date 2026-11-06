import Mathlib

theorem algebra_9157 {f : ℝ → ℝ} (hf : ∀ x, f x = 4^x - 6 * 2^x + 8) :
    (∀ x, -1 ≤ f x) ∧ f (Real.logb 2 3) = -1 := by
  constructor
  · -- Show that -1 ≤ f(x) for all x.
    intro x
    have h1 : f x = 4^x - 6 * 2^x + 8 := hf x
    rw [h1]
    have h3 : (4:ℝ) ^ x = ((2:ℝ) ^ x) ^ 2 := by
      calc
        (4:ℝ) ^ x = (2 ^ (2:ℝ)) ^ x := by norm_num
        _ = 2 ^ (2 * x:ℝ) := by rw [← Real.rpow_mul]; ring_nf; all_goals linarith
        _ = (2 ^ (x:ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
    have h4 : (4:ℝ) ^ x - 6 * (2:ℝ) ^ x + 8 ≥ -1 := by
      have h5 : (4:ℝ) ^ x = ((2:ℝ) ^ x) ^ 2 := h3
      rw [h5]
      have h6 : ((2:ℝ) ^ x) ^ 2 - 6 * (2:ℝ) ^ x + 8 ≥ -1 := by
        nlinarith [sq_nonneg ((2:ℝ) ^ x - 3)]
      linarith
    linarith
  · -- Prove that f(log_2 3) = -1.
    have h5 : f (Real.logb 2 3) = 4 ^ (Real.logb 2 3) - 6 * 2 ^ (Real.logb 2 3) + 8 := hf (Real.logb 2 3)
    rw [h5]
    have h6 : (2:ℝ) ^ (Real.logb 2 3:ℝ) = 3 := by
      rw [Real.rpow_logb]
      all_goals linarith
    have h7 : (4:ℝ) ^ (Real.logb 2 3:ℝ) = 9 := by
      have h8 : (4:ℝ) ^ (Real.logb 2 3:ℝ) = ((2:ℝ) ^ (2:ℝ)) ^ (Real.logb 2 3:ℝ) := by
        norm_num
      have h9 : ((2:ℝ) ^ (2:ℝ)) ^ (Real.logb 2 3:ℝ) = (2:ℝ) ^ (2 * Real.logb 2 3:ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
      have h10 : (2:ℝ) ^ (2 * Real.logb 2 3:ℝ) = ((2:ℝ) ^ (Real.logb 2 3:ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h8, h9, h10, h6]
      all_goals norm_num
      <;> linarith
    rw [h7, h6]
    all_goals norm_num
    <;> linarith