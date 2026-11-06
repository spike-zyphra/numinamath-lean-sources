import Mathlib

open Real

theorem inequalities_197947 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 := by
  have h1 : b = 2 - a := by linarith
  rw [h1]
  -- We have to show $\frac{1}{1 + a^n} + \frac{1}{1 + (2 - a)^n} \geq 1$.
  have h2 : 0 < a := by linarith
  have h3 : a < 2 := by nlinarith
  have h4 : 0 < (2 - a : ℝ) := by nlinarith
  have h5 : a * (2 - a : ℝ) ≤ 1 := by
    nlinarith [sq_nonneg (a - 1)]
  have h7 : a ^ n * (2 - a : ℝ) ^ n ≤ (1 : ℝ) := by
    have h8 : a * (2 - a : ℝ) ≤ 1 := h5
    have h9 : a ^ n * (2 - a : ℝ) ^ n = (a * (2 - a : ℝ)) ^ n := by
      rw [mul_pow]
    rw [h9]
    have h10 : (a * (2 - a : ℝ) ) ^ n ≤ (1 : ℝ) ^ n := by
      apply pow_le_pow_left
      all_goals
        nlinarith [show 0 ≤ a * (2 - a : ℝ) by nlinarith]
    have h11 : (1 : ℝ) ^ n = (1 : ℝ) := by
      simp
    linarith [h10, h11]
  have h8 : (1 / (1 + a ^ n) + 1 / (1 + (2 - a : ℝ) ^ n) ) ≥ (1 : ℝ) := by
    have h9 : (1 / (1 + a ^ n) + 1 / (1 + (2 - a : ℝ) ^ n) ) = ( (1 + (2 - a : ℝ) ^ n + 1 + a ^ n ) / ( (1 + a ^ n) * (1 + (2 - a : ℝ) ^ n ) ) ) := by
      field_simp
      <;> ring
    rw [h9]
    have h10 : (1 + (2 - a : ℝ) ^ n + 1 + a ^ n ) / ( (1 + a ^ n) * (1 + (2 - a : ℝ) ^ n ) ) ≥ (1 : ℝ) := by
      apply (le_div_iff₀ (by positivity)).mpr
      -- Show `Numerator ≥ Denominator`.
      nlinarith [sq_nonneg (a ^ n - (2 - a : ℝ) ^ n ), sq_nonneg (a - (2 - a : ℝ) ), sq_nonneg ( (a * (2 - a : ℝ) ) ^ n - 1 ), sq_nonneg (a * (2 - a : ℝ) - 1 ), Real.rpow_nonneg (show (0 : ℝ) ≤ a by linarith ) n, Real.rpow_nonneg (show (0 : ℝ) ≤ (2 - a) by nlinarith ) n, Real.rpow_nonneg (show (0 : ℝ) ≤ a * (2 - a) by nlinarith ) n, h7, sq_nonneg (a - 1) ]
    linarith
  exact h8