import Mathlib

open Real Set

theorem inequalities_315381 (x : ℝ) :
    sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10) > 10 ↔
    x > (5 / 4) * sqrt 15 ∨ x < (-5 / 4) * sqrt 15 := by
  constructor
  · -- Assume sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10) > 10 prove x > (5 / 4) * sqrt 15 ∨ x < (-5 / 4) * sqrt 15
    intro h
    have h1 : 0 ≤ x^2 + 6 * x + 10 := by 
      nlinarith [sq_nonneg (x + 3)]
    have h2 : 0 ≤ x^2 - 6 * x + 10 := by
      nlinarith [sq_nonneg (x - 3)]
    have h3 : sqrt (x ^ 2 + 6 * x + 10) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 6 * x + 10)
    have h4 : sqrt (x ^ 2 - 6 * x + 10) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 6 * x + 10)
    have h5 : (sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10))^2 > 100 := by
      have h6 : sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10) > 10 := h
      nlinarith [h6, mul_nonneg (Real.sqrt_nonneg (x^2 + 6 * x + 10)) (Real.sqrt_nonneg (x^2 - 6 * x + 10))]
    -- frequency let's solve the polynomial inequality
    have h7 : (x^2 + 6 * x + 10) * (x^2 - 6 * x + 10) > (40 - x^2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x^2 + 6 * x + 10), Real.sqrt_nonneg (x^2 - 6 * x + 10),
        sq_nonneg (sqrt (x^2 + 6 * x + 10) - sqrt (x^2 - 6 * x + 10)), sq_nonneg (x^2 + 6 * x + 10 - (x^2 - 6 * x + 10)), Real.sq_sqrt h1, Real.sq_sqrt h2, h5,
          mul_nonneg (Real.sqrt_nonneg (x^2 + 6 * x + 10)) (Real.sqrt_nonneg (x^2 - 6 * x + 10)), sq_nonneg (sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10) - 10)
        ]
    -- frequency solving the last inequality and rearranged to $x^2 > \frac{375}{16} $
    have h8 : x^2 > 375 / 16 := by
      nlinarith [h7]
    -- split by case
    by_cases h9 : x > 0
    · -- x > 0, so sqrt x^2 > 0
      have h10 : x^2 > 375 / 16 := h8
      have h11 : x > Real.sqrt (375 / 16) := by
        nlinarith [Real.sqrt_nonneg (375 / 16), Real.sq_sqrt (show (0 : ℝ) ≤ 375 / 16 by norm_num : (0 : ℝ) ≤ 375 / 16), h10]
      have h12 : Real.sqrt (375 / 16) = (5 / 4) * Real.sqrt 15 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      left
      nlinarith [h11, h12]
    · -- x ≤ 0
      have h10 : x^2 > 375 / 16 := h8
      have h11 : x < -Real.sqrt (375 / 16) := by
        nlinarith [Real.sqrt_nonneg (375 / 16), Real.sq_sqrt (show (0 : ℝ) ≤ 375 / 16 by norm_num : (0 : ℝ) ≤ 375 / 16), h10]
      have h12 : Real.sqrt (375 / 16) = (5 / 4) * Real.sqrt 15 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      right
      nlinarith [h11, h12]
  · -- Assume x > (5 / 4) * sqrt 15 ∨ x < (-5 / 4) * sqrt 15 prove sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10) > 10
    rintro (h | h)
    · -- x > (5 / 4) * sqrt 15
      have h1 : x^2 > 375 / 16 := by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), sq_nonneg (x - (5 / 4) * Real.sqrt 15), sq_nonneg (x), sq_nonneg ((5 / 4) * Real.sqrt 15), h]
      have h3 : 0 ≤ x^2 + 6 * x + 10 := by 
        nlinarith [sq_nonneg (x + 3)]
      have h4 : 0 ≤ x^2 - 6 * x + 10 := by
        nlinarith [sq_nonneg (x - 3)]
      have h5 : (sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10))^2 > 100 := by
        nlinarith [Real.sqrt_nonneg (x^2 + 6 * x + 10), Real.sqrt_nonneg (x^2 - 6 * x + 10), Real.sq_sqrt h3, Real.sq_sqrt h4, mul_nonneg (Real.sqrt_nonneg (x^2 + 6 * x + 10)) (Real.sqrt_nonneg (x^2 - 6 * x + 10)), sq_nonneg (sqrt (x^2 + 6 * x + 10) - sqrt (x^2 - 6 * x + 10)), sq_nonneg (x^2 + 6 * x + 10 - (x^2 - 6 * x + 10)), h1]
      nlinarith [Real.sqrt_nonneg (x^2 + 6 * x + 10), Real.sqrt_nonneg (x^2 - 6 * x + 10), Real.sq_sqrt h3, Real.sq_sqrt h4, h5]
    · -- x < (-5 / 4) * sqrt 15
      have h1 : x^2 > 375 / 16 := by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), sq_nonneg (x + (5 / 4) * Real.sqrt 15), sq_nonneg (x), sq_nonneg ((-5 / 4) * Real.sqrt 15), h]
      have h3 : 0 ≤ x^2 + 6 * x + 10 := by 
        nlinarith [sq_nonneg (x + 3)]
      have h4 : 0 ≤ x^2 - 6 * x + 10 := by
        nlinarith [sq_nonneg (x - 3)]
      have h5 : (sqrt (x^2 + 6 * x + 10) + sqrt (x^2 - 6 * x + 10))^2 > 100 := by
        nlinarith [Real.sqrt_nonneg (x^2 + 6 * x + 10), Real.sqrt_nonneg (x^2 - 6 * x + 10), Real.sq_sqrt h3, Real.sq_sqrt h4, mul_nonneg (Real.sqrt_nonneg (x^2 + 6 * x + 10)) (Real.sqrt_nonneg (x^2 - 6 * x + 10)), sq_nonneg (sqrt (x^2 + 6 * x + 10) - sqrt (x^2 - 6 * x + 10)), sq_nonneg (x^2 + 6 * x + 10 - (x^2 - 6 * x + 10)), h1]
      nlinarith [Real.sqrt_nonneg (x^2 + 6 * x + 10), Real.sqrt_nonneg (x^2 - 6 * x + 10), Real.sq_sqrt h3, Real.sq_sqrt h4, h5]