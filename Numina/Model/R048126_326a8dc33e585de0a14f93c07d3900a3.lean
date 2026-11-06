import Mathlib

theorem algebra_2150
    (a : ℝ)
    (h : ∃ x0 x1 : ℝ, x0 ≠ x1 ∧ 9 * x0 ^ 2 - 6 * (a + 1) * x0 + a ^ 2 - 3 = 0 ∧ 9 * x1 ^ 2 - 6 * (a + 1) * x1 + a ^ 2 - 3 = 0 ∧ x0 * x1 = 1) :
    a = 2 * Real.sqrt 3 := by
  rcases h with ⟨x0, x1, hx01, h0, h1, h2⟩
  have h3 : (x0 - x1) ≠ 0 := by intro h'; apply hx01; linarith
  have h4 : 9 * (x0 + x1) - 6 * (a + 1) = 0 := by
    have h5 : 9 * (x0 ^ 2 - x1 ^ 2) - 6 * (a + 1) * (x0 - x1) = 0 := by
      nlinarith
    have h6 : (x0 - x1) * (9 * (x0 + x1) - 6 * (a + 1)) = 0 := by
      ring_nf at h5 ⊢
      linarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- h7: x0 - x1 = 0
      exfalso
      apply hx01
      linarith
    · -- h8: 9*(x0+x1) -6*(a+1) = 0
      linarith
  have h7 : (a^2) = 12 := by
    nlinarith [sq_pos_of_ne_zero (show x0 - x1 ≠ 0 by exact h3), sq_nonneg (x0 - x1), sq_nonneg (x0 + x1)]
  have h8 : (a - 2 * Real.sqrt 3) * (a + 2 * Real.sqrt 3) = 0 := by
    have h9 : a ^ 2 = 12 := h7
    have h10 : Real.sqrt 3 ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (a)]
  cases' (mul_eq_zero.1 h8) with h10 h11
  · -- Case where $a - 2 \sqrt{3} = 0$, so $a = 2 \sqrt{3}$, which is the desired result.
    linarith
  · -- Case where $a + 2 \sqrt{3} = 0$, so $a = -2 \sqrt{3}$, which needs to be shown as a contradiction.
    have h12 : a = -2 * Real.sqrt 3 := by linarith
    -- Substitute the value of `a` into the equations `h0` and `h1`.
    rw [h12] at h0 h1
    -- Show a contradiction through nonlinear arithmetic.
    -- The equations would result in a contradition for the squared roots of negative values.
    -- The equations would result in squared terms contradicting in combination.
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_pos_of_ne_zero (show x0 - x1 ≠ 0 by exact h3), sq_nonneg (x0 + x1), sq_nonneg (x0 - x1), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]