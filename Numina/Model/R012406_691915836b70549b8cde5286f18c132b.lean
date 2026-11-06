import Mathlib

theorem algebra_319182 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y = x * y) (h2 : x + y + z = x * y * z) :
    z ∈ Set.Ioc 1 (4 / 3) := by
  have h3 : 0 < x * y := by
    nlinarith
  have h4 : (x * y - 1) > 0 := by
    nlinarith [sq_nonneg (x - y), h1, mul_pos hx hy]
  have eq1 : z = (x + y) / (x * y - 1) := by
    have h3' : x * y * z - z = x + y := by linarith [h2, h1]
    have h6 : z * (x * y - 1) = x + y := by linarith [h3']
    have h7 : z = (x + y) / (x * y - 1) := by
      field_simp [(show x * y - 1 ≠ 0 by nlinarith)]
      <;> linarith
    exact h7
  constructor
  · -- Prove z > 1
    have h9 : z > 1 := by
      rw [eq1] at hz
      have h9 : (x + y : ℝ) / (x * y - 1) > 1 := by
        apply (lt_div_iff₀ (by nlinarith)).mpr 
        nlinarith [h1, mul_pos hx hy, sq_nonneg (x - y)]
      linarith
    linarith
  · -- Prove z ≤ 4 / 3
    have h8 : z ≤ 4 / 3 := by
      have h9 : z = (x + y) / (x * y - 1) := eq1
      have h10 : (x + y) / (x * y - 1) ≤ 4 / 3 := by
        have h7 : x * y - 1 > 0 := h4
        apply (div_le_iff₀ h7).mpr
        have h11 : x * y ≥ 4 := by 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 4), mul_pos hx hy, sq_nonneg (x - 2), sq_nonneg (y - 2), h1, sq_nonneg (x * y - 4), mul_pos hx hy, sq_nonneg (x - y)]
        nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), h1, mul_pos hx hy, sq_nonneg (x * y - 4), h11, mul_pos hx hy]
      linarith [h9, h10]
    linarith