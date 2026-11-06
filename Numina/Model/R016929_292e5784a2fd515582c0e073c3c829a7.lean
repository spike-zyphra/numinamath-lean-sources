import Mathlib

open Real

theorem algebra_9819 {x : ℝ} (hx : 0 < x) :
    logb 9 (x^2 + 32) + logb 9 27 - 2 * logb 9 x = 2 ↔ x = 4 := by
  constructor
  · -- Forward direction: If the equation holds, then x = 4.
    intro h
    have h1 : logb 9 (x^2 + 32) + logb 9 27 - 2 * logb 9 x = logb 9 ((x ^ 2 + 32) * 27 / x^2) := by
      have h2 : 2 * logb 9 x = logb 9 (x ^ 2) := by
        simp [logb_pow]
        <;> ring_nf <;> norm_num
      have h3 : logb 9 (x^2 + 32) + logb 9 27 = logb 9 ((x ^ 2 + 32) * 27) := by 
        rw [← logb_mul (by nlinarith) (by norm_num)]
      calc 
        logb 9 (x^2 + 32) + logb 9 27 - 2 * logb 9 x 
          = (logb 9 (x^2 + 32) + logb 9 27) - (2 * logb 9 x) := by ring
        _ = logb 9 ((x^2 + 32) * 27) - (logb 9 (x^2)) := by 
          rw [h2, h3]
        _ = logb 9 ((x ^ 2 + 32) * 27 / x ^ 2) := by 
          rw [← logb_div (by positivity) (by positivity)]
          <;> ring_nf <;> positivity
    rw [h1] at h
    have h2 : ((x ^ 2 + 32) * 27 / x ^ 2) = (81 : ℝ) := by
      have h3 : logb 9 ((x ^ 2 + 32) * 27 / x ^ 2) = 2 := h
      have h4 : ((x ^ 2 + 32) * 27 / x ^ 2) = (9: ℝ) ^ (2: ℝ) := by
        rw [logb_eq_iff_rpow_eq] at h3
        · -- Show that (x ^ 2 + 32) * 27 / x ^ 2 = 9 ^ 2
          nlinarith
        all_goals try positivity
        all_goals try nlinarith
      norm_num at h4 ⊢
      <;> nlinarith
    have h3 : (x ^ 2 + 32) * 27 = 81 * (x ^ 2) := by
      have h4 : ((x ^ 2 + 32) * 27 / x ^ 2) = (81 : ℝ) := h2
      have hx2_pos : 0 < x^2 := by
        nlinarith
      field_simp at h4
      nlinarith
    have h4 : x ^ 2 = 16 := by
      nlinarith
    have h5 : x = 4 := by
      nlinarith
      all_goals try positivity
    exact h5
  · -- Reverse direction: If x = 4, then the equation holds.
    intro h
    rw [h]
    have h1 : logb 9 (4^2 + 32) + logb 9 27 - 2 * logb 9 4 = 2 := by
      have h2 : logb 9 (4^2 + 32) + logb 9 27 = logb 9 ((4 ^ 2 + 32) * 27) := by
        rw [← logb_mul (by norm_num) (by norm_num)]
      have h3 : 2 * logb 9 4 = logb 9 (4 ^ 2) := by
        simp [logb_pow]
        <;> ring_nf <;> norm_num
      have h5 : logb 9 (4 ^ 2 + 32) + logb 9 27 - 2 * logb 9 4 = logb 9 ((4 ^ 2 + 32) * 27 / (4 ^ 2 : ℝ)) := by 
        calc 
          logb 9 (4 ^ 2 + 32) + logb 9 27 - 2 * logb 9 4 
            = (logb 9 (4 ^ 2 + 32) + logb 9 27) - (2 * logb 9 4) := by ring
          _ = logb 9 ((4 ^ 2 + 32) * 27) - (logb 9 (4 ^ 2)) := by 
            rw [h3, h2]
          _ = logb 9 ((4 ^ 2 + 32) * 27 / (4 ^ 2 : ℝ)) := by 
            rw [← logb_div (by positivity) (by positivity)]
            <;> ring_nf <;> positivity
      have h6 : ((4 ^ 2 + 32 : ℝ) * 27 / (4 ^ 2 : ℝ)) = (81 : ℝ) := by
        norm_num
      have h7 : logb (9 : ℝ) (81 : ℝ) = (2 : ℝ) := by
        rw [logb_eq_iff_rpow_eq] <;> (norm_num)
        <;> ring_nf <;> norm_num
      rw [h5, h6, h7]
    linarith [h1]