import Mathlib

open Real Set

theorem inequalities_311802 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ x * y * z) :
    (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ sqrt 3 ∧
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z ≥ x * y * z ∧
    (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) = sqrt 3 := by
  have h1 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ sqrt 3 := by
    have h2 : x * y * z > 0 := by
      apply mul_pos
      apply mul_pos
      exact hx
      exact hy
      exact hz
    have h3 : (x ^ 2 + y ^ 2 + z ^ 2) ≥ sqrt 3 * (x * y * z) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - x * y * z), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), 
          sq_nonneg (z * x - x * y), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num),
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z by linarith)
        ]
    have h4 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ sqrt 3 := by
      have h5 : (x * y * z) > 0 := h2
      apply (le_div_iff₀ (h5)).mpr
      linarith
    linarith
  have h5 : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z ≥ x * y * z ∧
    (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) = sqrt 3 := by
    use Real.sqrt 3, Real.sqrt 3, Real.sqrt 3
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    constructor
    · -- Show z > 0
      positivity
    constructor
    · -- Show x + y + z ≥ x * y * z
      have h6 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
      have h7 : (Real.sqrt 3 + Real.sqrt 3 + Real.sqrt 3 : ℝ) = 3 * Real.sqrt 3 := by ring
      have h8 : (Real.sqrt 3 * Real.sqrt 3 * Real.sqrt 3 : ℝ) = 3 * Real.sqrt 3 := by
        calc
          (Real.sqrt 3 * Real.sqrt 3 * Real.sqrt 3 : ℝ) = ( (Real.sqrt 3) ^ 2 ) * Real.sqrt 3 := by ring
          _ = (3 : ℝ) * Real.sqrt 3 := by rw [h6]
          _ = (3 * Real.sqrt 3 : ℝ) := by ring
      linarith [h7, h8]
    · -- Show (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) = sqrt 3
      have h6 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
      have h7 : (Real.sqrt 3 : ℝ) ^ 3 = (3 * Real.sqrt 3 : ℝ) := by
        calc 
          (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3 : ℝ) * (Real.sqrt 3 : ℝ) ^ 2 := by ring
          _ = (Real.sqrt 3 : ℝ) * (3 : ℝ) := by rw [h6]
          _ = (3 * Real.sqrt 3 : ℝ) := by ring
      field_simp [h6, show (Real.sqrt 3 * Real.sqrt 3 * Real.sqrt 3 : ℝ) = 3 * Real.sqrt 3 by
        calc
          (Real.sqrt 3 * Real.sqrt 3 * Real.sqrt 3 : ℝ) = ( (Real.sqrt 3) ^ 2 ) * Real.sqrt 3 := by ring
          _ = (3 : ℝ) * Real.sqrt 3 := by rw [h6]
          _ = (3 * Real.sqrt 3 : ℝ) := by ring
        ]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  constructor
  · exact h1
  · exact h5