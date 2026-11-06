import Mathlib

theorem algebra_209323 {n : ℕ} (hn : n ≥ 2) (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x = 672 * y) (h : (n.choose 2) * x^2 * y^2 + (n.choose 3) * x^3 * y^3 = 0) :
    (n.choose 2018) * x^2018 * y^2018 = -1356096 * y^2018 := by
  have hx_eq : x = 672 * y := hxy 
  rw [hx_eq] at h
  have eq1 : (n.choose 2 : ℝ) * (672 * y) ^ 2 * y^2 + (n.choose 3 : ℝ) * (672 * y) ^ 3 * y^3 = 0 := by 
    linarith
  ring_nf at eq1 ⊢
  have h6 : n ≥ 2 := by omega
  by_cases h7 : n ≥ 3
  · -- n ≥ 3
    have h8 : (n.choose 2 : ℝ) > 0 := by
      have h3 : n.choose 2 > 0 := by 
        apply Nat.choose_pos
        all_goals omega
      exact_mod_cast h3
    have h9 : (n.choose 3 : ℝ) > 0 := by
      have h4 : n.choose 3 > 0 := by 
        apply Nat.choose_pos
        all_goals omega
      exact_mod_cast h4
    have eq5 : y = 0 := by
      have h8 : y ^ 4 = 0 := by
        nlinarith [sq_nonneg (y ^ 2), sq_nonneg ((n.choose 2) * y ^ 2), sq_nonneg ((n.choose 3) * y ^ 2), sq_nonneg (y ^ 2), sq_nonneg (y ^ 3), mul_pos h8 (show 0 < (672 : ℝ) ^ 2 by positivity), mul_pos h9 (show 0 < (672 : ℝ) ^ 3 by positivity)]
      have : y = 0 := by
        have h8' : y ^ 4 = 0 := h8 
        have : y ^ 2 = 0 := by
          nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y)]
        have : y = 0 := by
          nlinarith [sq_nonneg (y)]
        assumption 
      assumption
    contradiction
  · -- n < 3, so n = 2 
    have h8 : n = 2 := by 
      omega 
    rw [h8] at eq1
    have h6 : y ^ 4 = 0 := by
      norm_num [Nat.choose] at eq1 
      nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y ^ 3), sq_nonneg (y ^ 4), sq_pos_of_ne_zero (show y ≠ 0 by exact hy)]
    have eq5 : y = 0 := by
      have h8 : y ^ 4 = 0 := h6 
      have : y = 0 := by
        have h8' : y ^ 4 = 0 := h8 
        have : y ^ 2 = 0 := by
          nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y)]
        have : y = 0 := by
          nlinarith [sq_nonneg (y)]
        assumption 
      assumption 
    contradiction