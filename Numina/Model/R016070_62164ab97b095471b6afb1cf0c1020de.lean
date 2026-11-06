import Mathlib

theorem inequalities_86407 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + z * x) + 1 / (z ^ 2 + x * y) ≤
    ((1 / (x * y) + 1 / (y * z) + 1 / (z * x)) / 2) := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < y * z := mul_pos hy hz
  have h3 : 0 < z * x := mul_pos hz hx

  have h4 : 1 / (x ^ 2 + y * z) ≤ (1 / (4 * x * y) + 1 / (4 * x * z)) := by
    have h5 : 0 < x ^ 2 + y * z := by positivity
    have h6 : 0 < 4 * x * y := by positivity
    have h7 : 0 < 4 * x * z := by positivity
    have h8 : 1 / (x ^ 2 + y * z) - (1/ (4 * x * y) + 1/ (4 * x * z)) ≤ 0 := by
      have h9 : 1 / (x ^ 2 + y * z) - (1/ (4 * x * y) + 1/ (4 * x * z)) = (4 * x * y * z - (x ^ 2 + y * z) * (y + z)) / ((x ^ 2 + y * z) * 4 * x * y * z) := by
        field_simp
        ring
      rw [h9]
      have h10 : 4 * x * y * z - (x ^ 2 + y * z) * (y + z) ≤ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), sq_nonneg (x * y - x * z), sq_nonneg (x * z - y * z), sq_nonneg (y * z - x * y),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
      have h11 : (x ^ 2 + y * z) * 4 * x * y * z > 0 := by positivity
      have h12 : (4 * x * y * z - (x ^ 2 + y * z) * (y + z)) / ((x ^ 2 + y * z) * 4 * x * y * z) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · positivity
      linarith
    linarith

  have h5 : 1 / (y ^ 2 + z * x) ≤ (1 / (4 * y * z) + 1 / (4 * y * x)) := by
    have h8 : 0 < y ^ 2 + z * x := by positivity
    have h9 : 0 < 4 * y * z := by positivity
    have h10 : 0 < 4 * y * x := by positivity
    have h11 : 1 / (y ^ 2 + z * x) - (1/ (4 * y * z) + 1/ (4 * y * x)) ≤ 0 := by
      have h12 : 1 / (y ^ 2 + z * x) - (1/ (4 * y * z) + 1/ (4 * y * x)) = (4 * y * z * x - (y ^ 2 + z * x) * (z + x)) / ((y ^ 2 + z * x) * 4 * y * z * x) := by
        field_simp
        ring
      rw [h12]
      have h13 : 4 * y * z * x - (y ^ 2 + z * x) * (z + x) ≤ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), sq_nonneg (x * y - x * z), sq_nonneg (x * z - y * z), sq_nonneg (y * z - x * y),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]
      have h14 : (y ^ 2 + z * x) * 4 * y * z * x > 0 := by positivity
      have h15 : (4 * y * z * x - (y ^ 2 + z * x) * (z + x)) / ((y ^ 2 + z * x) * 4 * y * z * x) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · positivity
      linarith
    linarith

  have h6 : 1 / (z ^ 2 + x * y) ≤ (1 / (4 * z * x) + 1 / (4 * z * y)) := by
    have h7 : 0 < z ^ 2 + x * y := by positivity
    have h8 : 0 < 4 * z * x := by positivity
    have h9 : 0 < 4 * z * y := by positivity
    have h10 : 1 / (z ^ 2 + x * y) - (1/ (4 * z * x) + 1/ (4 * z * y)) ≤ 0 := by
      have h11 : 1 / (z ^ 2 + x * y) - (1/ (4 * z * x) + 1/ (4 * z * y)) = (4 * z * x * y - (z ^ 2 + x * y) * (x + y)) / ((z ^ 2 + x * y) * 4 * z * x * y) := by
        field_simp
        ring
      rw [h11]
      have h12 : 4 * z * x * y - (z ^ 2 + x * y) * (x + y) ≤ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), sq_nonneg (x * y - x * z), sq_nonneg (x * z - y * z), sq_nonneg (y * z - x * y),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]
      have h13 : (z ^ 2 + x * y) * 4 * z * x * y > 0 := by positivity
      have h14 : (4 * z * x * y - (z ^ 2 + x * y) * (x + y)) / ((z ^ 2 + x * y) * 4 * z * x * y) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · positivity
      linarith
    linarith

  have h7 : 1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + z * x) + 1 / (z ^ 2 + x * y) ≤ (1 / (4 * x * y) + 1 / (4 * x * z)) + (1 / (4 * y * z) + 1 / (4 * y * x)) + (1 / (4 * z * x) + 1 / (4 * z * y)) := by
    linarith [h4, h5, h6]

  have h8 : (1 / (4 * x * y) + 1 / (4 * x * z)) + (1 / (4 * y * z) + 1 / (4 * y * x)) + (1 / (4 * z * x) + 1 / (4 * z * y)) = (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) / 2 := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> nlinarith
  linarith [h7, h8]