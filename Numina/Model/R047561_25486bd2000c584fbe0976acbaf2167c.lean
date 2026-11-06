import Mathlib

/- Given that $x$, $y$, $z$ are positive real numbers, and satisfy $x^{\lg x}y^{\lg y}z^{\lg z}=5$, $x^{\lg yz}y^{\lg zx}z^{\lg xy}=2$, then $xyz=$ ___          ___. -/
theorem algebra_11134 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x ^ (Real.logb 10 x) * y ^ (Real.logb 10 y) * z ^ (Real.logb 10 z) = 5)
    (h2 : x ^ (Real.logb 10 (y * z)) * y ^ (Real.logb 10 (z * x)) * z ^ (Real.logb 10 (x * y)) = 2) :
    x * y * z = 10 ∨ x * y * z = 1 / 10 := by

  have h1' : Real.logb 10 (x ^ (Real.logb 10 x) * y ^ (Real.logb 10 y) * z ^ (Real.logb 10 z)) = Real.logb 10 5 := by
    rw [h1]

  have h2' : Real.logb 10 (x ^ (Real.logb 10 (y * z)) * y ^ (Real.logb 10 (z * x)) * z ^ (Real.logb 10 (x * y))) = Real.logb 10 2 := by
    rw [h2]

  have h3 : Real.logb 10 (x ^ (Real.logb 10 x) * y ^ (Real.logb 10 y) * z ^ (Real.logb 10 z)) =
    Real.logb 10 (x ^ (Real.logb 10 x)) + Real.logb 10 (y ^ (Real.logb 10 y)) + Real.logb 10 (z ^ (Real.logb 10 z)) := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h4 : Real.logb 10 (x ^ (Real.logb 10 (y * z)) * y ^ (Real.logb 10 (z * x)) * z ^ (Real.logb 10 (x * y))) =
    Real.logb 10 (x ^ (Real.logb 10 (y * z))) + Real.logb 10 (y ^ (Real.logb 10 (z * x))) + Real.logb 10 (z ^ (Real.logb 10 (x * y))) := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h5 : Real.logb 10 (x ^ (Real.logb 10 x)) = Real.logb 10 x * Real.logb 10 x := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h6 : Real.logb 10 (y ^ (Real.logb 10 y)) = Real.logb 10 y * Real.logb 10 y := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h7 : Real.logb 10 (z ^ (Real.logb 10 z)) = Real.logb 10 z * Real.logb 10 z := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h8 : Real.logb 10 (x ^ (Real.logb 10 (y * z))) = Real.logb 10 (y * z) * Real.logb 10 x := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h9 : Real.logb 10 (y ^ (Real.logb 10 (z * x))) = Real.logb 10 (z * x) * Real.logb 10 y := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h10 : Real.logb 10 (z ^ (Real.logb 10 (x * y))) = Real.logb 10 (x * y) * Real.logb 10 z := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith

  have h11 : Real.logb 10 (y * z) = Real.logb 10 y + Real.logb 10 z := by
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h12 : Real.logb 10 (z * x) = Real.logb 10 z + Real.logb 10 x := by
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h13 : Real.logb 10 (x * y) = Real.logb 10 x + Real.logb 10 y := by
    rw [Real.logb_mul (by positivity) (by positivity)]

  rw [h3] at h1'
  rw [h4] at h2'

  rw [h5, h6, h7] at h1'
  rw [h8, h9, h10] at h2'

  rw [h11, h12, h13] at h2'

  have h5 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z) ^ 2 = 1 := by
    have h6 : Real.logb 10 5 + Real.logb 10 2 = 1 := by
      have h7 : Real.logb 10 5 + Real.logb 10 2 = Real.logb 10 (5 * 2) := by
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      have h8 : Real.logb 10 (5 * 2) = 1 := by
        norm_num [Real.logb_eq_iff_rpow_eq]
      linarith [h7, h8]
    nlinarith [h1', h2', h6]

  have h6 : Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = 1 ∨
      Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = -1 := by
    have h7 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z) ^ 2 = 1 := h5
    have h8 : Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = 1 ∨
        Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = -1 := by
      have h9 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z - 1) * (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z + 1) = 0 := by
        nlinarith [h7]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · left
        linarith
      · right
        linarith
    exact h8

  cases' h6 with h7 h8
  · -- $\log_{10}(x \cdot y \cdot z) = 1$, so $x \cdot y \cdot z = 10$
    have h9 : Real.logb 10 (x * y * z) = 1 := by
      have h10 : Real.logb 10 (x * y * z) = Real.logb 10 x + Real.logb 10 y + Real.logb 10 z := by
        simp [Real.logb_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]
      linarith [h10, h7]
    have h10 : x * y * z = 10 := by
      have h11 : x * y * z = 10 ^ (Real.logb 10 (x * y * z)) := by
        field_simp [Real.rpow_logb, hx, hy, hz]
      rw [h9] at h11
      norm_num at h11 ⊢
      linarith
    left
    linarith
  · -- $\log_{10}(x \cdot y \cdot z) = -1$, so $x \cdot y \cdot z = \frac{1}{10}$
    have h9 : Real.logb 10 (x * y * z) = -1 := by
      have h10 : Real.logb 10 (x * y * z) = Real.logb 10 x + Real.logb 10 y + Real.logb 10 z := by
        simp [Real.logb_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]
      linarith [h10, h8]
    have h11 : x * y * z = 10 ^ (Real.logb 10 (x * y * z)) := by
      field_simp [Real.rpow_logb, hx, hy, hz]
    rw [h9] at h11
    have h12 : x * y * z = 1 / 10 := by
      norm_num at h11 ⊢
      linarith
    right
    linarith