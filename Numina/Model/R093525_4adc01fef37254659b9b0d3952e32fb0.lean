import Mathlib

theorem inequalities_603377 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt (x^2 + y^2) + Real.sqrt (y^2 + z^2) + Real.sqrt (z^2 + x^2) ≥
    Real.sqrt 2 * (x + y + z) := by
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → Real.sqrt (x^2 + y^2) ≥ (x + y) / Real.sqrt 2 := by
    intro x y hx hy
    have h6 : Real.sqrt 2 > 0 := by
      positivity
    have h7 : ((x + y) / Real.sqrt 2) ≤ Real.sqrt (x^2 + y^2) := by
      have h8 : ((x + y) / Real.sqrt 2) ^ 2 ≤ (x^2 + y^2) := by
        have h4 : ((x + y) / Real.sqrt 2) ^ 2 = (x + y) ^ 2 / (Real.sqrt 2) ^ 2 := by
          field_simp
          <;> ring_nf <;> norm_num
          all_goals linarith
        have h5 : (Real.sqrt 2) ^ 2 = 2 := by
          exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        rw [h4, h5]
        nlinarith [sq_nonneg (x - y)]
      have h9 : Real.sqrt (((x + y) / Real.sqrt 2) ^ 2) ≤ Real.sqrt (x^2 + y^2) := by
        apply Real.sqrt_le_sqrt
        all_goals nlinarith [sq_nonneg (x - y)]
      have h3 : Real.sqrt (((x + y) / Real.sqrt 2) ^ 2) = (x + y) / Real.sqrt 2 := by
        rw [Real.sqrt_sq]
        all_goals positivity
      linarith [h3, h9]
    linarith
  have hxy : Real.sqrt (x^2 + y^2) ≥ (x + y) / Real.sqrt 2 := h1 x y hx hy
  have hyz : Real.sqrt (y^2 + z^2) ≥ (y + z) / Real.sqrt 2 := h1 y z hy hz
  have hzx : Real.sqrt (z^2 + x^2) ≥ (z + x) / Real.sqrt 2 := h1 z x hz hx
  have h2 : Real.sqrt 2 > 0 := by positivity
  have h3 : (x + y) / Real.sqrt 2 + (y + z) / Real.sqrt 2 + (z + x) / Real.sqrt 2 = Real.sqrt 2 * (x + y + z) := by
    field_simp
    <;> ring_nf <;> norm_num
    all_goals linarith
  linarith [hxy, hyz, hzx, h3, Real.sqrt_nonneg (x^2 + y^2), Real.sqrt_nonneg (y^2 + z^2), Real.sqrt_nonneg (z^2 + x^2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]