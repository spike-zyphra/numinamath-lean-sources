import Mathlib
/-6. Irrational equation
$$ 2x^2 - 15x - \sqrt{2x^2 - 15x + 1998} = -18 $$
The solution is-/
theorem algebra_314650 (x : ℝ) (hx : 2 * x ^ 2 - 15 * x + 1998 ≥ 0) :
    2 * x ^ 2 - 15 * x - Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = -18 ↔
    x = -3 / 2 ∨ x = 9 := by
  constructor
  · -- Forward direction: assume the equation holds, prove x = -3/2 or x = 9
    intro h
    have h1 : 2 * x ^ 2 - 15 * x + 1998 ≥ 0 := hx
    have h2 : Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = 2 * x ^ 2 - 15 * x + 18 := by linarith
    have h3 : 2 * x^2 - 15 * x + 18 ≥ 0 := by
      have h3 : Real.sqrt (2 * x ^ 2 - 15 * x + 1998) ≥ 0 := Real.sqrt_nonneg (2 * x ^ 2 - 15 * x + 1998)
      linarith [h2, h3]
    have h4 : (Real.sqrt (2 * x ^ 2 - 15 * x + 1998)) ^ 2 = (2 * x ^ 2 - 15 * x + 18) ^ 2 := by
      rw [h2]
    have h5 : (Real.sqrt (2 * x ^ 2 - 15 * x + 1998)) ^ 2 = 2 * x ^ 2 - 15 * x + 1998 := Real.sq_sqrt (by linarith)
    have h6 : (2 * x ^ 2 - 15 * x + 18) ^ 2 = (2 * x^2 - 15 * x + 18) ^ 2 := by rfl
    rw [h5] at h4
    have h7 : (2 * x^2 - 15 * x + 18) ^ 2 = 2 * x^2 - 15 * x + 1998 := by linarith [h4, h6]
    have h8 : (2 * x^2 - 15 * x + 18) ^ 2 - (2 * x^2 - 15 * x + 1998) = 0 := by linarith [h7]
    have h9 : 4 * x^4 - 60 * x^3 + 295 * x^2 - 525 * x - 1674 = 0 := by
      ring_nf at h8
      nlinarith
    have h10 : (2 * x^2 - 15 * x - 27) * (2 * x^2 - 15 * x + 62) = 0 := by
      ring_nf
      linarith [h9]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case 1: 2x^2 - 15x - 27 = 0
      have h13 : 2 * x^2 - 15 * x - 27 = 0 := h11
      have h14 : (2 * x + 3) * (x - 9) = 0 := by
        ring_nf
        linarith [h13]
      cases' (mul_eq_zero.mp h14) with h15 h16
      · -- Subcase 1.1: 2x + 3 = 0
        have hx1 : x = -3 / 2 := by linarith
        left
        exact hx1
      · -- Subcase 1.2: x - 9 = 0
        have hx2 : x = 9 := by linarith
        right
        exact hx2
    · -- Case 2: 2x^2 - 15x + 62 = 0
      have h17 : 2 * x^2 - 15 * x + 62 = 0 := h12
      have h18 : x^2 - (15 / 2) * x + 31 = 0 := by
        linarith [h17]
      have h19 : (x - 15 / 4) ^ 2 ≥ 0 := sq_nonneg (x - 15 / 4)
      nlinarith [sq_nonneg (x - 15 / 4), Real.sqrt_nonneg (2 * x^2 - 15 * x + 1998), h2, h17]
  · -- Backward direction: assume x = -3/2 or x = 9, prove the equation holds
    rintro (hx | hx)
    · -- x = -3/2
      rw [hx]
      have h1 : Real.sqrt (2 * (-3 / 2:ℝ) ^ 2 - 15 * (-3 / 2) + 1998) = 45 := by
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      rw [h1]
      norm_num
    · -- x = 9
      rw [hx]
      have h1 : Real.sqrt (2 * (9:ℝ) ^ 2 - 15 * (9:ℝ) + 1998) = 45 := by
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      rw [h1]
      norm_num
