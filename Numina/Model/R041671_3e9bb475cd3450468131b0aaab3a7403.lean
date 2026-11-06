import Mathlib

open Real

theorem inequalities_220275 :
    IsLeast {(x * y / z + y * z / x + z * x / y) | (x : ℝ) (y: ℝ) (z: ℝ) (_: 0 < x) (_: 0 < y) (_: 0 < z) (_: x^2 + y^2 + z^2 = 1)} (√3) := by
  constructor
  · -- Show that √3 is in the set.
    refine' ⟨1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3,
      ?_, ?_, ?_, ?_, ?_⟩
    · -- Show 0 < 1 / Real.sqrt 3
      positivity
    · -- Show 0 < 1 / Real.sqrt 3
      positivity
    · -- Show 0 < 1 / Real.sqrt 3
      positivity
    · -- Show (1 / Real.sqrt 3 : ℝ) ^ 2 + (1 / Real.sqrt 3 : ℝ) ^ 2 + (1 / Real.sqrt 3 : ℝ) ^ 2 = 1
      have h1 : Real.sqrt 3 > 0 := by
        positivity
      have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      field_simp [h1, h1, h1]
      <;> nlinarith [h2, Real.sqrt_nonneg 3]
    · -- Show (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) / (1 / Real.sqrt 3 : ℝ) + (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) / (1 / Real.sqrt 3 : ℝ) + (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) / (1 / Real.sqrt 3 : ℝ) = Real.sqrt 3
      have h1 : Real.sqrt 3 > 0 := by
        positivity
      have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      field_simp [h1, h1, h1]
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Show that √3 is minimal
    intro r hr 
    rcases hr with ⟨x, y, z, hx, hy, hz, h1, hr⟩
    have h2 : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
      have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
        have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 * ((x * y / z) * (y * z / x) + (y * z / x) * (z * x / y) + (z * x / y) * (x * y / z)) := by
          nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y), sq_nonneg (z * x / y - x * y / z), 
            sq_nonneg (x * y / z * (x * y / z)), sq_nonneg (y * z / x * (y * z / x)), sq_nonneg (z * x / y * (z * x / y)), 
            mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
            mul_pos (show 0 < y * z by nlinarith) (show 0 < x * z by nlinarith)
          ]
        have h4 : (x * y / z) * (y * z / x) + (y * z / x) * (z * x / y) + (z * x / y) * (x * y / z) = (x^2 + y^2 + z^2) := by 
          field_simp
          <;> nlinarith
        rw [h4] at h3
        nlinarith [h1]
      have h3' : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
        have h2' : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ (3 : ℝ) := h3
        have h5 : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) ≥ Real.sqrt (3 : ℝ) := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ (x * y / z + y * z / x + z * x / y) ^ 2 by linarith)
        have h6 : Real.sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) = (x * y / z + y * z / x + z * x / y) := by
          rw [Real.sqrt_sq (show (x * y / z + y * z / x + z * x / y) ≥ 0 by positivity)]
        rw [h6] at h5
        linarith
      linarith
    have h1 : (x * y / z + y * z / x + z * x / y) = r := by 
      linarith [hr]
    nlinarith [h2, h1, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]