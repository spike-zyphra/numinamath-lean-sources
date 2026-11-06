import Mathlib

open BigOperators Real Set

theorem algebra_138369 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b)
  (h : logb a b = -2) :
  a + b ≥ 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 := by
  have h1 : a > 0 := ha.1
  have h2 : a ≠ 1 := ha.2
  have h3 : logb a b = (log b) / (log a) := by
    field_simp [logb]
  rw [h3] at h
  have h4 : log a ≠ 0 := by
    by_contra h4
    have h5 : a = 1 := by
      rw [Real.log_eq_zero] at h4
      rcases h4 with (r | r | r)
      · linarith
      · linarith
      · linarith
    have h7 : a = 1 := h5
    have h8 : a ≠ 1 := h2
    contradiction
  have h5 : log b = -2 * log a := by
    have h7 : log a ≠ 0 := h4
    field_simp at h ⊢
    linarith
  have h6 : b = a ^ (-2 : ℝ) := by
    have h7 : log b = -2 * log a := h5
    have h8 : b = Real.exp (log b) := by
      rw [Real.exp_log]
      all_goals linarith
    have h9 : Real.exp (log b) = Real.exp (-2 * log a) := by
      rw [h7]
    have h10 : Real.exp (-2 * log a) = (Real.exp (log a)) ^ (-2 : ℝ) := by
      rw [← Real.exp_mul]
      ring_nf
    have h11 : Real.exp (log a) = a := by
      rw [Real.exp_log]
      all_goals linarith
    rw [h8, h9, h10, h11]
  have h7 : a > 0 := ha.1
  have h8 : b > 0 := hb
  -- Now we need to minimize $a + b = a + a^{-2}$.
  -- Let's write $a + b = a + a^{-2}$.
  have h101 : a + b = a + a ^ (-2 : ℝ) := by
    rw [h6]
  have h102 : a + a ^ (-2 : ℝ) ≥ 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 := by
    have h12 : a + a ^ (-2 : ℝ) = a + 1 / (a ^ 2) := by
      have h98 : a ^ (-2 : ℝ) = 1 / (a ^ 2) := by
        have h101 : a ^ (-2 : ℝ) = (a ^ (2 : ℝ))⁻¹ := by
          rw [← Real.rpow_neg]
          ring_nf
          all_goals linarith
        have h102 : (a ^ (2 : ℝ)) = a ^ 2 := by
          norm_cast
        rw [h102] at h101
        rw [h101]
        all_goals
          try { field_simp }
      rw [h98]
    rw [h12]
    -- Now we need to minimize $a + \frac{1}{a^2}$.
    -- To minimize $a + \frac{1}{a^2}$, take the derivative and set it to zero:
    -- The derivative is $1 - \frac{2}{a^3}$.
    -- Setting $1 - \frac{2}{a^3} = 0 \implies a^3 = 2$.
    -- So $a = 2^{1/3}$, and the minimum value is $3/2 \cdot 2^{1/3}$.
    have h100 : a + 1 / (a ^ 2) ≥ 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 := by
      have h101 : a + 1 / (a ^ 2) - 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 ≥ 0 := by
        have h140 : a + 1 / (a ^ 2) - 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 =
            (2 * a ^ 3 + 2 - 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) * a ^ 2) / (2 * a ^ 2) := by
          field_simp
          nlinarith
        rw [h140]
        have h1000 : 2 * a ^ 3 + 2 - 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) * a ^ 2 ≥ 0 := by
          have h1300 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals positivity
          nlinarith [sq_nonneg (a ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) * a ^ 2), sq_nonneg (a ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), sq_nonneg (a ^ 3 - 2), sq_nonneg (a ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3) * a), sq_nonneg (a - (2 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg (a ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 3)), Real.rpow_pos_of_pos (show 0 < (2 : ℝ) by linarith) (1 / 3), Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by linarith) (1 / 3), sq_nonneg (a * (a - (2 : ℝ) ^ ((1 : ℝ) / 3)))]
        have h10000 : 2 * a ^ 3 + 2 - 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) * a ^ 2 ≥ 0 := h1000
        have h10001 : (2 * a ^ 3 + 2 - 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) * a ^ 2) / (2 * a ^ 2) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    linarith
  linarith [h101, h102]