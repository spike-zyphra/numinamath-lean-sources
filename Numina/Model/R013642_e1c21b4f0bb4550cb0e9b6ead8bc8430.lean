import Mathlib


theorem algebra_8919
    (a b c : ℝ × ℝ)
    (h₀ : a.1 + b.1 + c.1 = 0 ∧ a.2 + b.2 + c.2 = 0)
    (h₁ : (a.1 - b.1) * (a.1 - c.1) + (a.2 - b.2) * (a.2 - c.2) = 0)
    (h₂ : Real.sqrt ((b.1 - c.1)^2 + (b.2 - c.2)^2) = 9) :
    Real.sqrt (a.1^2 + a.2^2) + Real.sqrt (b.1^2 + b.2^2) + Real.sqrt (c.1^2 + c.2^2) ≤ 3 + 3 * Real.sqrt 10 := by

  have h2' : (b.1 - c.1)^2 + (b.2 - c.2)^2 = 81 := by
    calc
      (b.1 - c.1)^2 + (b.2 - c.2)^2 = (Real.sqrt ((b.1 - c.1)^2 + (b.2 - c.2)^2))^2 := by rw [Real.sq_sqrt]; positivity
      _ = 9^2 := by rw [h₂]
      _ = (81 : ℝ) := by norm_num

  have h3 : a.1 + b.1 + c.1 = 0 := h₀.1
  have h4 : a.2 + b.2 + c.2 = 0 := h₀.2

  have ha1 : a.1 = -b.1 - c.1 := by linarith
  have ha2 : a.2 = -b.2 - c.2 := by linarith

  rw [ha1] at h₁
  rw [ha2] at h₁

  have h5 : 2 * (b.1 ^ 2 + b.2 ^ 2) + 2 * (c.1 ^ 2 + c.2 ^ 2) + 5 * (b.1 * c.1 + b.2 * c.2) = 0 := by
    nlinarith

  have h6 : (b.1 ^ 2 + b.2 ^ 2) + (c.1 ^ 2 + c.2 ^ 2) - 2 * (b.1 * c.1 + b.2 * c.2) = 81 := by
    nlinarith

  have h7 : b.1 * c.1 + b.2 * c.2 = -18 := by
    nlinarith

  have h8 : (b.1 ^ 2 + b.2 ^ 2) + (c.1 ^ 2 + c.2 ^ 2) = 45 := by
    linarith

  have h9 : a.1 ^ 2 + a.2 ^ 2 = 9 := by
    rw [ha1, ha2]
    nlinarith [h7, h8]

  have ha : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [h9]

  have h11 : Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2) ≤ 3 * Real.sqrt 10 := by
    have h10 : (Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2 ≤ 90 := by
      have h11 : (Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2 =
          (Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) ^ 2 + (Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2 + 2 * (Real.sqrt (b.1 ^ 2 + b.2 ^ 2) * Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) := by ring
      rw [h11]
      have h12 : (Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) ^ 2 = b.1 ^ 2 + b.2 ^ 2 := Real.sq_sqrt (by positivity)
      have h13 : (Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2 = c.1 ^ 2 + c.2 ^ 2 := Real.sq_sqrt (by positivity)
      rw [h12, h13]
      nlinarith [sq_nonneg (b.1 ^ 2 + b.2 ^ 2 - c.1 ^ 2 - c.2 ^ 2), sq_nonneg (b.1 * c.1 + b.2 * c.2), Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (b.1 * c.1 + b.2 * c.2), mul_nonneg (Real.sqrt_nonneg (b.1 ^ 2 + b.2 ^ 2)) (Real.sqrt_nonneg (c.1 ^ 2 + c.2 ^ 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    have h14 : (Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2 ≤ 9 * 10 := by
      nlinarith

    have h15 : Real.sqrt ((Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2) ≤ Real.sqrt (9 * 10) := Real.sqrt_le_sqrt h14
    have h16 : Real.sqrt (9 * 10) = 3 * Real.sqrt 10 := by
      calc
        Real.sqrt (9 * 10) = Real.sqrt (3 ^ 2 * 10) := by ring_nf
        _ = (3 : ℝ) * Real.sqrt 10 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have h17 : Real.sqrt ((Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2)) ^ 2) = Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2) := by
      rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (b.1 ^ 2 + b.2 ^ 2) + Real.sqrt (c.1 ^ 2 + c.2 ^ 2) by positivity)]
    rw [h17] at h15
    rw [h16] at h15
    linarith

  linarith [ha, h11]