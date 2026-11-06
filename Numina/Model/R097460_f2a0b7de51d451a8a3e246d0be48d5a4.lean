import Mathlib

theorem algebra_186790 (a : ℝ) (ha : 0 < a) (h : (1 / 2) * a * (a ^ 2 + 1) = ∫ x in (0)..a, x ^ 2 + 1) :
    a = Real.sqrt 3 := by
  have h1 : ∫ x in (0)..a, x^2 + 1 = (a ^ 3 + 3 * a) / 3 := by
    norm_num
    -- Compute integral of x^2 + 1 from 0 to a
    -- ∫ (x^2 + 1) dx = (x^3/3 + x)
    -- Evaluating from 0 to a: (a^3/3 + a) - (0 + 0)
    -- = a^3/3 + a = (a^3 + 3a)/3
    simp [intervalIntegral.integral_const, mul_comm]
    <;> ring_nf <;> simp [pow_three]
    <;> ring
  rw [h1] at h
  have h2 : a^3 - 3 * a = 0 := by
    nlinarith [h]
  have h3 : a * (a^2 - 3) = 0 := by
    linarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where `a = 0` which contradicts `0 < a`.
    linarith
  · -- Case where `a^2 - 3 = 0`.
    have h7 : a^2 = 3 := by linarith
    have h8 : a = Real.sqrt 3 := by
      have h9 : a > 0 := ha
      have h10 : a = Real.sqrt (a^2) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_pos h9]
      rw [h7] at h10
      exact h10
    exact h8