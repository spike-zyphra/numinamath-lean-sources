import Mathlib

open Real

theorem algebra_12097 :
    IsLeast {((x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1)) / (x * y * z) |
      (x : ℝ) (y : ℝ) (z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)} 125 := by
  constructor
  · -- Show that 125 is in the set
    use 1, 1, 1
    norm_num
  · -- Show that 125 is the minimum
    intro w hw
    rcases hw with ⟨x, y, z, hx, hy, hz, hw⟩
    have h1 : 0 < x * y * z := by
      positivity
    have h2 : x ^ 2 + 3 * x + 1 ≥ 5 * x := by
      nlinarith [sq_nonneg (x - 1)]
    have h3 : y ^ 2 + 3 * y + 1 ≥ 5 * y := by
      nlinarith [sq_nonneg (y - 1)]
    have h4 : z ^ 2 + 3 * z + 1 ≥ 5 * z := by
      nlinarith [sq_nonneg (z - 1)]
    have h5 : (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1) ≥ 125 * (x * y * z) := by
      have eq2 : x ^ 2 + 3 * x + 1 ≥ 5 * x := h2
      have eq3 : y ^ 2 + 3 * y + 1 ≥ 5 * y := h3
      have eq4 : z ^ 2 + 3 * z + 1 ≥ 5 * z := h4
      have eq5 : (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) ≥ (5 * x) * (5 * y) := by
        nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      have eq6 : (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1) ≥ (5 * x) * (5 * y) * (5 * z) := by
        nlinarith [eq5, eq4, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      nlinarith
    have h6 : (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1) / (x * y * z) ≥ 125 := by
      have h5 : (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1) ≥ 125 * (x * y * z) := h5
      have h6 : 0 < (x * y * z) := h1
      have h7 : (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1) / (x * y * z) ≥ 125 * (x * y * z) / (x * y * z) := by
        apply (div_le_div_right h6).mpr
        nlinarith
      have eq8 : 125 * (x * y * z) / (x * y * z) = 125 := by
        field_simp
        <;> nlinarith
      linarith [h7, eq8]
    linarith [hw, h6]