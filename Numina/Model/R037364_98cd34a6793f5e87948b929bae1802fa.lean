import Mathlib

theorem algebra_113414 (x : ℝ) (hx : x^2 + 4 > 0 ∧ x > 0) :
    Real.logb 2 (x^2 + 4) - Real.logb 2 x + x^2 - 4 * x + 2 = 0 ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, show x = 2
    intro h_eq
    have h1 : x ^ 2 + 4 > 0 := hx.1
    have h2 : x > 0 := hx.2
    have h3 : Real.logb 2 (x^2 + 4) - Real.logb 2 x = Real.logb 2 ((x ^ 2 + 4) / x) := by
      rw [← Real.logb_div (by positivity) (by positivity)]
    have h4 : Real.logb 2 (x^2 + 4) - Real.logb 2 x + x^2 - 4 * x + 2 = 0 := h_eq
    have h5 : Real.logb 2 ((x^2 + 4) / x) = -x^2 + 4 * x - 2 := by
      nlinarith [h3, h4]
    -- minimized at x = 2
    have h9 : Real.logb 2 ((x ^ 2 + 4) / x) ≥ 2 := by
      have h10 : (x ^ 2 + 4) / x ≥ 4 := by
        have h11 : x > 0 := h2
        have : (x ^ 2 + 4) ≥ 4 * x := by
          nlinarith [sq_nonneg ((x - 2) : ℝ)]
        have h36 : (x ^ 2 + 4) / x ≥ 4 := by
          have h14 : (x ^ 2 + 4) ≥ 4 * x := by
            nlinarith
          have h24 : x > 0 := h2
          apply (le_div_iff₀ (by positivity)).mpr
          nlinarith
        linarith
      have h40 : Real.logb (2 : ℝ) (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h11 : Real.logb (2 : ℝ) ((x ^ 2 + 4) / x) ≥ Real.logb (2 : ℝ) (4 : ℝ) := by
        apply Real.logb_le_logb_of_le
        all_goals
          have h39 : x ^ 2 + 4 > 0 := by positivity
          have h40 : x > 0 := h2
          all_goals
            try positivity
            try nlinarith
      linarith [h40, h11]
    -- right side is max at x = 2
    have h15 : -x^2 + 4 * x - 2 ≤ 2 := by
      nlinarith [sq_nonneg ((x - 2) : ℝ)]
    have h10 : Real.logb 2 ((x ^ 2 + 4) / x) = 2 := by
      nlinarith [h5, h15, h9]
    have h12 : (x ^ 2 + 4) / x = 4 := by
      have h13 : Real.logb 2 ((x ^ 2 + 4) / x) = 2 := h10
      have h37 : (x ^ 2 + 4) / x = (2 : ℝ) ^ (2 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] at h13
        · linarith
        all_goals
          have h39 : x ^ 2 + 4 > 0 := by positivity
          have h40 : x > 0 := h2
          all_goals
            try positivity
            try nlinarith
      have h36 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
        norm_num
      rw [h36] at h37
      linarith
    have h14 : x ^ 2 + 4 = 4 * x := by
      have h30 : x > 0 := h2
      have h31 : (x ^ 2 + 4) / x = 4 := h12
      field_simp at h31 ⊢
      nlinarith
    have h16 : (x - 2) ^ 2 = 0 := by
      nlinarith
    have h03 : x - 2 = 0 := by
      apply pow_eq_zero
      exact h16
    linarith
  · -- Assume x = 2, show the equation holds
    intro h_eq
    rw [show x = 2 by linarith [h_eq]]
    have h7 : Real.logb 2 (2 ^ 2 + 4) - Real.logb 2 (2 : ℝ) + (2 : ℝ) ^ 2 - 4 * (2 : ℝ) + 2 = 0 := by
      have h1 : Real.logb 2 (2 ^ 2 + 4) = 3 := by
        norm_num
        have h4 : Real.logb 2 8 = 3 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith [h4]
      have h2 : Real.logb 2 (2 : ℝ) = 1 := by
        rw [Real.logb_self_eq_one]
        all_goals norm_num
      rw [h1, h2]
      norm_num
    linarith