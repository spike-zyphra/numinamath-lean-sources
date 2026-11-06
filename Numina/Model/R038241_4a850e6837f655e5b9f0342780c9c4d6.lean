import Mathlib

open Real

theorem inequalities_306796 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x^2 + y^2) ^ ((1 : ℝ) / 2) > (x^3 + y^3) ^ ((1 : ℝ) / 3) := by
  have h2 : (x^2 + y^2 : ℝ) ^ 3 > (x^3 + y^3 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y), mul_pos hx hy, pow_pos hx 2, pow_pos hx 3, pow_pos hx 4, pow_pos hx 5, pow_pos hx 6, pow_pos hy 2, pow_pos hy 3, pow_pos hy 4, pow_pos hy 5, pow_pos hy 6, mul_pos (show 0 < x * y by nlinarith) (show 0 < x * y by nlinarith)]
  have hx2_pos : 0 < (x^2 + y^2 : ℝ) := by positivity
  have hy2_pos : 0 < (x^3 + y^3 : ℝ) := by positivity
  have h3 : (x^2 + y^2 : ℝ) ^ ((1 : ℝ) / 2) > (x^3 + y^3 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h41 : (x^2 + y^2 : ℝ) ^ ((1 : ℝ) / 2) = ((x^2 + y^2) ^ 3) ^ ((1 : ℝ) / 6) := by 
      have h111 : ((x^2 + y^2 : ℝ) ^ 3) ^ ((1 : ℝ) / 6) = (x^2 + y^2) ^ ((1 : ℝ) / 2) := by 
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith [show 0 < (x^2 + y^2 : ℝ) by positivity]
      linarith [h111]
    have h51 : (x^3 + y^3 : ℝ) ^ ((1 : ℝ) / 3) = ((x^3 + y^3) ^ 2) ^ ((1 : ℝ) / 6) := by
      have h112 : ((x^3 + y^3 : ℝ) ^ 2) ^ ((1 : ℝ) / 6) = (x^3 + y^3) ^ ((1 : ℝ) / 3) := by 
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith [show 0 < (x^3 + y^3 : ℝ) by positivity]
      linarith [h112]
    rw [h41, h51]
    -- Now we need to prove that `((x^2+y^2)^3)^(1/6) > ((x^3+y^3)^2)^(1/6)`
    -- This is equivalent to proving that $A^3 > B^2$ where $A = x^2+y^2$, $B = x^3+y^3$.
    -- This is precisely what `h2` establishes.
    have h61 : ((x^2 + y^2) ^ 3) ^ ((1 : ℝ) / 6) > ((x^3 + y^3) ^ 2) ^ ((1 : ℝ) / 6) := by
      have h71 : (x^2 + y^2 : ℝ) ^ 3 > (x^3 + y^3 : ℝ) ^ 2 := h2
      have h81 : 0 < (x^2 + y^2 : ℝ) ^ 3 := by positivity
      have h91 : 0 < (x^3 + y^3 : ℝ) ^ 2 := by positivity
      have h10 : ((x^2 + y^2 : ℝ) ^ 3) ^ ((1 : ℝ) / 6) > ((x^3 + y^3 : ℝ) ^ 2) ^ ((1 : ℝ) / 6) := by
        apply Real.rpow_lt_rpow
        all_goals
          nlinarith [h71, h81, h91]
      linarith [h10]
    linarith
  linarith [h3]