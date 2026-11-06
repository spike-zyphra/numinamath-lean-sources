import Mathlib

theorem inequalities_58458 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = 1) :
    1 ≤ x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) ∧
    x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) ≤ 9 / 8 := by

  have h1 : 0 < 1 - y * z := by 
    nlinarith [sq_nonneg (x + y + z - 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h2 : 0 < 1 - z * x := by 
    nlinarith [sq_nonneg (x + y + z - 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h3 : 0 < 1 - x * y := by 
    nlinarith [sq_nonneg (x + y + z - 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

  constructor
  · -- Prove the lower bound: 1 ≤ x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y)
    have h4 : x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) ≥ 1 := by
      have h5 : x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) - 1 ≥ 0 := by
        have h6 : x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) - 1 =
            (x * (1 - z * x) * (1 - x * y) + y * (1 - y * z) * (1 - x * y) + z * (1 - y * z) * (1 - z * x) - (1 - y * z) * (1 - z * x) * (1 - x * y)) / ((1 - y * z) * (1 - z * x) * (1 - x * y)) := by 
          field_simp
          <;> ring
        rw [h6] at *
        have h7 : 0 < (1 - y * z) * (1 - z * x) * (1 - x * y) := by positivity
        have h8 : x * (1 - z * x) * (1 - x * y) + y * (1 - y * z) * (1 - x * y) + z * (1 - y * z) * (1 - z * x) - (1 - y * z) * (1 - z * x) * (1 - x * y) ≥ 0 := by
          have h9 : z = 1 - x - y := by linarith
          rw [h9]
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
            mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith), 
            mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
            mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ x * (1 - x - y) by nlinarith), 
            mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ y * (1 - x - y) by nlinarith)]
        apply div_nonneg
        linarith
        all_goals positivity 
      linarith 
    linarith 
  · -- Prove the upper bound: x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) ≤ 9 / 8 
    have h5 : x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) ≤ 9 / 8 := by
      have h61 : 0 < (1 - y * z) * (1 - z * x) * (1 - x * y) := by positivity
      have h77 : x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) - 9 / 8 ≤ 0 := by 
        have h777 : x / (1 - y * z) + y / (1 - z * x) + z / (1 - x * y) - 9 / 8 = 
          (8 * x * (1 - z * x) * (1 - x * y) + 8 * y * (1 - y * z) * (1 - x * y) + 8 * z * (1 - y * z) * (1 - z * x) - 9 * (1 - y * z) * (1 - z * x) * (1 - x * y)) / (8 * (1 - y * z) * (1 - z * x) * (1 - x * y)) := by 
          field_simp
          <;> ring 
        rw [h777]
        have h88 : 0 < 8 * (1 - y * z) * (1 - z * x) * (1 - x * y) := by positivity 
        have h99 : 8 * x * (1 - z * x) * (1 - x * y) + 8 * y * (1 - y * z) * (1 - x * y) + 8 * z * (1 - y * z) * (1 - z * x) - 9 * (1 - y * z) * (1 - z * x) * (1 - x * y) ≤ 0 := by 
          have h90 : z = 1 - x - y := by linarith 
          rw [h90] 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
            mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith), 
            mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
            mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ x * (1 - x - y) by nlinarith), 
            mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ y * (1 - x - y) by nlinarith), 
            sq_nonneg (x * y - y * (1 - x - y)), sq_nonneg (y * (1 - x - y) - (1 - x - y) * x), sq_nonneg ((1 - x - y) * x - x * y)]
        apply div_nonpos_of_nonpos_of_nonneg 
        linarith 
        all_goals positivity 
      linarith 
    linarith