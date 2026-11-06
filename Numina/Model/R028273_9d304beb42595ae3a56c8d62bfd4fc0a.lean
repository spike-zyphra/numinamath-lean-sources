import Mathlib

theorem inequalities_89372 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    ((x + 1) / x) ^ 2 + ((y + 1) / y) ^ 2 ≥ 18 := by
  have h6 : ((x + 1) / x) ^ 2 + ((y + 1) / y) ^ 2 - 18 ≥ 0 := by
    have hx2 : 0 < x := hx
    have hy2 : 0 < y := hy
    have h7 : x + 1 > 0 := by linarith
    have h8 : y + 1 > 0 := by linarith
    have hx1 : x > 0 := by linarith
    have hy1 : y > 0 := by linarith
    have h9 : y = 1 - x := by linarith
    rw [h9]
    have hx3 : 0 < x := by linarith
    have h10 : 0 < 1 - x := by
      nlinarith [show (x < 1) from by nlinarith]
    have h11 : x * (1 - x) > 0 := by
      positivity
    have h12 : ((x + 1) / x) ^ 2 + (( (1 - x) + 1) / (1 - x)) ^ 2 - 18 ≥ 0 := by
      have h13 : 0 < x := by linarith
      have h14 : 0 < 1 - x := by
        nlinarith [show (x < 1) from by nlinarith]
      have h15 : x * (1 - x) > 0 := by
        positivity
      have h16 : ((x + 1) / x) ^ 2 + (( (1 - x) + 1) / (1 - x)) ^ 2 - 18 =
          ( (x + 1)^2 / x^2 ) + ( (2 - x)^2 / (1 - x)^2 ) - 18 := by
        field_simp [h13, h14]
        <;> ring_nf
      rw [h16]
      have h17 : ( (x + 1)^2 / x^2 ) + ( (2 - x)^2 / (1 - x)^2 ) - 18 ≥ 0 := by
        have h18 : 0 < x^2 * (1 - x)^2 := by positivity
        have h19 : ( (x + 1)^2 / x^2 ) + ( (2 - x)^2 / (1 - x)^2 ) - 18 =
            ( (x + 1)^2 * (1 - x)^2 + (2 - x)^2 * x^2 - 18 * x^2 * (1 - x)^2 ) / (x^2 * (1 - x)^2 ) := by
          field_simp [h13, h14]
          <;> ring
        rw [h19]
        have h20 : (x ^ 2 * (1 - x) ^ 2 ) > 0 := by positivity
        have h21 : (x + 1)^2 * (1 - x)^2 + (2 - x)^2 * x^2 - 18 * x^2 * (1 - x)^2 ≥ 0 := by
          nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x - 1 / 2), sq_nonneg (x - 2), sq_nonneg (x * (1 - x) - 1 / 9), sq_nonneg (x * (1 - x) - 4 / 9), mul_pos hx2 (show (0 : ℝ) < 1 - x by nlinarith), sq_nonneg (x * (1 - x) - 4 / 9), sq_nonneg ((1 - x) - 2 / 3) ]
        apply div_nonneg
        · -- Show that numerator is ≥ 0.
          nlinarith
        · -- Show that denominator is > 0.
          positivity
      linarith
    linarith
  linarith