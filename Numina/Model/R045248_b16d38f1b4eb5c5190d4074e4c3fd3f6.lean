import Mathlib

theorem algebra_144843 {x y : ℝ} (hx : 3 * x + Real.sqrt (3 * x - y) + y = 6) (hy : 9 * x ^ 2 + 3 * x - y - y ^ 2 = 36) :
    (x = 2 ∧ y = -3) ∨ (x = 6 ∧ y = -18) := by
  by_cases h' : 3 * x - y ≥ 0
  · -- Assume 3 * x - y ≥ 0, so √(3 * x - y) is valid
    have h5 : Real.sqrt (3 * x - y) ≥ 0 := by positivity
    have h6 : (Real.sqrt (3 * x - y)) ^ 2 = 3 * x - y := Real.sq_sqrt h'
    have eq1 : 3 * x + Real.sqrt (3 * x - y) + y = 6 := hx
    have eq2 : 9 * x ^ 2 + 3 * x - y - y ^ 2 = 36 := hy
    have eq3 : (Real.sqrt (3 * x - y)) ^ 2 = 3 * x - y := by
      rw [Real.sq_sqrt]
      nlinarith
    have eq4 : Real.sqrt (3 * x - y) ^ 3 - 7 * Real.sqrt (3 * x - y) ^ 2 + 36 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 3), sq_nonneg (Real.sqrt (3 * x - y) - 3), sq_nonneg (Real.sqrt (3 * x - y) - 6)]
    have h9 : (Real.sqrt (3 * x - y) - 3) * (Real.sqrt (3 * x - y) - 6) * (Real.sqrt (3 * x - y) + 2) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    cases' (mul_eq_zero.mp h10) with h12 h13
    · -- Real.sqrt (3 * x - y) - 3 = 0
      have ht1 : Real.sqrt (3 * x - y) = 3 := by linarith
      have hx1 : x = 2 := by
        nlinarith [Real.sqrt_nonneg (3 * x - y), sq_nonneg (y + 3), h5]
      have hy1 : y = -3 := by
        nlinarith [Real.sqrt_nonneg (3 * x - y), hx1, ht1, h5]
      left
      exact ⟨hx1, hy1⟩
    · -- Real.sqrt (3 * x - y) - 6 = 0
      have ht2 : Real.sqrt (3 * x - y) = 6 := by linarith
      have hx2 : x = 6 := by
        nlinarith [Real.sqrt_nonneg (3 * x - y), sq_nonneg (y + 18), h5]
      have hy2 : y = -18 := by
        nlinarith [Real.sqrt_nonneg (3 * x - y), hx2, ht2, h5]
      right
      exact ⟨hx2, hy2⟩
    · -- Real.sqrt (3 * x - y) + 2 = 0
      have ht3 : Real.sqrt (3 * x - y) = -2 := by linarith
      nlinarith [Real.sqrt_nonneg (3 * x - y), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x - y) by linarith)]
  · -- Assume 3 * x - y < 0. Then √(3 * x - y) is not defined.
    have h14 : Real.sqrt (3 * x - y) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
    rw [h14] at hx
    nlinarith