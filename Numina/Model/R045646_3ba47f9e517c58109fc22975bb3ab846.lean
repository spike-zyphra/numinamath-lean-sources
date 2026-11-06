import Mathlib


open Real


theorem inequalities_599789 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    sqrt (x / (y + z)) + sqrt (y / (z + x)) + sqrt (z / (x + y)) ≥ 2 := by
  have h4 : 0 < x * y * z := by positivity
  have h5 : 0 < y + z := by positivity
  have h6 : 0 < z + x := by positivity
  have h7 : 0 < x + y := by positivity
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz

  have h8 : sqrt (x / (y + z)) ≥ 2 * x / (x + y + z) := by
    have h16 : (sqrt (x / (y + z)) ) ^ 2 ≥ (2 * x / (x + y + z)) ^ 2 := by
      have h12 : (sqrt (x / (y + z)) ) ^ 2 = x / (y + z) := by
        rw [Real.sq_sqrt]
        positivity
      have h13 : (2 * x / (x + y + z)) ^ 2 = 4 * x^2 / (x + y + z)^2 := by
        field_simp
        <;> nlinarith
      rw [h12, h13]
      have h14 : x / (y + z) - 4 * x^2 / (x + y + z)^2 ≥ 0 := by
        have pos1 : 0 < (y + z) * (x + y + z) ^ 2 := by positivity
        have h15 : x / (y + z) - 4 * x^2 / (x + y + z) ^ 2 =
            (x * (x + y + z) ^ 2 - 4 * x^2 * (y + z)) / ((y + z) * (x + y + z) ^ 2) := by
          field_simp
          ring
        rw [h15]
        have h16 : x * (x + y + z) ^ 2 - 4 * x^2 * (y + z) ≥ 0 := by
          nlinarith [sq_nonneg (x - y - z)]
        apply div_nonneg
        linarith
        all_goals nlinarith
      nlinarith
    have h14 : sqrt (x / (y + z)) ≥ 0 := by positivity
    have h15 : (2 * x / (x + y + z : ℝ)) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (x / (y + z))]

  have h9 : sqrt (y / (z + x)) ≥ 2 * y / (x + y + z) := by
    have h16 : (sqrt (y / (z + x)) ) ^ 2 ≥ (2 * y / (x + y + z)) ^ 2 := by
      have h19 : (sqrt (y / (z + x)) ) ^ 2 = y / (z + x) := by
        rw [Real.sq_sqrt]
        positivity
      have h20 : (2 * y / (x + y + z)) ^ 2 = 4 * y^2 / (x + y + z)^2 := by
        field_simp
        <;> nlinarith
      rw [h19, h20]
      have h21 : y / (z + x) - 4 * y^2 / (x + y + z)^2 ≥ 0 := by
        have pos1 : 0 < (z + x) * (x + y + z) ^ 2 := by positivity
        have h22 : y / (z + x) - 4 * y^2 / (x + y + z) ^ 2 =
            (y * (x + y + z) ^ 2 - 4 * y^2 * (z + x)) / ((z + x) * (x + y + z) ^ 2) := by
          field_simp
          ring
        rw [h22]
        have h23 : y * (x + y + z) ^ 2 - 4 * y^2 * (z + x) ≥ 0 := by
          nlinarith [sq_nonneg (y - x - z)]
        apply div_nonneg
        linarith
        all_goals nlinarith
      nlinarith
    have h14 : sqrt (y / (z + x)) ≥ 0 := by positivity
    have h15 : (2 * y / (x + y + z : ℝ)) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (y / (z + x))]

  have h10 : sqrt (z / (x + y)) ≥ 2 * z / (x + y + z) := by
    have h26 : (sqrt (z / (x + y)) ) ^ 2 ≥ (2 * z / (x + y + z)) ^ 2 := by
      have h27 : (sqrt (z / (x + y)) ) ^ 2 = z / (x + y) := by
        rw [Real.sq_sqrt]
        positivity
      have h28 : (2 * z / (x + y + z)) ^ 2 = 4 * z^2 / (x + y + z)^2 := by
        field_simp
        <;> nlinarith
      rw [h27, h28]
      have h29 : z / (x + y) - 4 * z^2 / (x + y + z)^2 ≥ 0 := by
        have pos1 : 0 < (x + y) * (x + y + z) ^ 2 := by positivity
        have h30 : z / (x + y) - 4 * z^2 / (x + y + z) ^ 2 =
            (z * (x + y + z) ^ 2 - 4 * z^2 * (x + y)) / ((x + y) * (x + y + z) ^ 2) := by
          field_simp
          ring
        rw [h30]
        have h31 : z * (x + y + z) ^ 2 - 4 * z^2 * (x + y) ≥ 0 := by
          nlinarith [sq_nonneg (z - x - y)]
        apply div_nonneg
        linarith
        all_goals nlinarith
      nlinarith
    have h14 : sqrt (z / (x + y)) ≥ 0 := by positivity
    have h15 : (2 * z / (x + y + z : ℝ)) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (z / (x + y))]

  have h11 : sqrt (x / (y + z)) + sqrt (y / (z + x)) + sqrt (z / (x + y)) ≥
      2 * x / (x + y + z) + 2 * y / (x + y + z) + 2 * z / (x + y + z) := by
    linarith

  have h12 : 2 * x / (x + y + z) + 2 * y / (x + y + z) + 2 * z / (x + y + z) = 2 := by
    field_simp
    <;> nlinarith

  linarith