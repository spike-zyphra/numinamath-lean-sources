import Mathlib

theorem inequalities_173292 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 6 / y ^ 2 + y ^ 6 / x ^ 2 ≥ x ^ 4 + y ^ 4 := by 
  have h1 : x ^ 6 / y ^ 2 + y ^ 6 / x ^ 2 - (x ^ 4 + y ^ 4) ≥ 0 := by
    have h2 : x ^ 2 * y ^ 2 > 0 := by
      apply mul_pos
      · -- Show x^2 > 0
        apply pow_two_pos_of_ne_zero
        exact hx
      · -- Show y^2 > 0
        apply pow_two_pos_of_ne_zero
        exact hy

    have h3 : x ^ 6 / y ^ 2 + y ^ 6 / x ^ 2 - (x ^ 4 + y ^ 4) =
        (x ^ 8 + y ^ 8 - (x ^ 6 * y ^ 2 + x ^ 2 * y ^ 6)) / (x ^ 2 * y ^ 2) := by
      field_simp [pow_two, hy, hx]
      ring_nf

    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 4 + x ^ 2 * y ^ 2 + y ^ 4), sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2)]
    linarith
  linarith