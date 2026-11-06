import Mathlib

theorem inequalities_246089 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    abs (x / y + y / x) ≥ 2 := by
  have h1 : x / y + y / x = (x ^ 2 + y ^ 2) / (x * y) := by
    field_simp [show y ≠ 0 by assumption, show x ≠ 0 by assumption]
    <;> ring
  have h2 : abs (x / y + y / x) = abs ((x ^ 2 + y ^ 2) / (x * y)) := by
    rw [h1]
  have h3 : abs ((x ^ 2 + y ^ 2) / (x * y)) ≥ 2 := by
    have h4 : (x ^ 2 + y ^ 2) / (x * y) ≤ -2 ∨ (x ^ 2 + y ^ 2) / (x * y) ≥ 2 := by
      by_cases h5 : x * y > 0
      · -- If $xy > 0$, then $\frac{x^2 + y^2}{xy} \geq 2$.
        right
        have h6 : (x ^ 2 + y ^ 2) / (x * y) - 2 ≥ 0 := by
          have h7 : x ^ 2 + y ^ 2 - 2 * (x * y) ≥ 0 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
          have h8 : (x ^ 2 + y ^ 2) / (x * y) - 2 = (x ^ 2 + y ^ 2 - 2 * (x * y)) / (x * y) := by 
            field_simp [show x ≠ 0 by assumption, show y ≠ 0 by assumption]
            <;> ring
          rw [h8]
          apply div_nonneg
          linarith
          linarith
        linarith
      · -- If $xy ≤ 0$, then we have $x \ne 0 $ and $ y \ne 0 $, so $ xy < 0 $ or $ xy = 0 $, the latter is impossible.
        have h6 : x * y < 0 := by
          by_contra h
          push_neg at h
          have : x * y = 0 := by nlinarith
          cases' (mul_eq_zero.mp this) with h7 h8
          · -- x=0: impossible
            exfalso
            apply hx
            linarith
          · -- y=0: impossible
            exfalso
            apply hy
            linarith
        have h7 : (x ^ 2 + y ^ 2) / (x * y) ≤ -2 := by
          have h8 : (x ^ 2 + y ^ 2) / (x * y) - (-2) ≤ 0 := by
            have h9 : x ^ 2 + y ^ 2 + 2 * (x * y) ≥ 0 := by
              nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
            have h10 : (x ^ 2 + y ^ 2) / (x * y) - (-2) = (x ^ 2 + y ^ 2 + 2 * (x * y)) / (x * y) := by 
              field_simp [show x ≠ 0 by assumption, show y ≠ 0 by assumption]
              <;> ring
            rw [h10]
            apply div_nonpos_of_nonneg_of_nonpos
            linarith
            nlinarith
          linarith
        left
        linarith
    cases h4 with
    | inl h =>
      rw [abs_of_nonpos (by linarith)]
      linarith
    | inr h =>
      rw [abs_of_nonneg (by linarith)]
      linarith
  linarith [h3, h2]