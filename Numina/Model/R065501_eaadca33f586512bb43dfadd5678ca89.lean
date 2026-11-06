import Mathlib

theorem algebra_161293 : (Real.sqrt (21 + 8 * Real.sqrt 5) / (4 + Real.sqrt 5)) * (Real.sqrt (9 - 4 * Real.sqrt 5)) = Real.sqrt 5 - 2 := by
  have h1 : Real.sqrt (21 + 8 * Real.sqrt 5) = 4 + Real.sqrt 5 := by
    have h2 : (4 + Real.sqrt 5) ^ 2 = 21 + 8 * Real.sqrt 5 := by
      calc
        (4 + Real.sqrt 5) ^ 2 = 4 ^ 2 + 8 * Real.sqrt 5 + Real.sqrt 5 ^ 2 := by ring
        _ = 16 + 8 * Real.sqrt 5 + (Real.sqrt 5 ^ 2) := by ring
        _ = 16 + 8 * Real.sqrt 5 + 5 := by rw [Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
        _ = 21 + 8 * Real.sqrt 5 := by ring
    have h3 : 4 + Real.sqrt 5 ≥ 0 := by
      positivity
    rw [←h2]
    field_simp [Real.sqrt_sq h3]
  have h3 : Real.sqrt (21 + 8 * Real.sqrt 5) / (4 + Real.sqrt 5) = 1 := by
    rw [h1]
    field_simp [show 4 + Real.sqrt 5 ≠ 0 by positivity]
    <;> nlinarith
    <;> ring_nf <;> norm_num
  have h4 : Real.sqrt (9 - 4 * Real.sqrt 5) = Real.sqrt 5 - 2 := by
    have h5 : (Real.sqrt 5 - 2) ^ 2 = 9 - 4 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 - 2) ^ 2 = Real.sqrt 5 ^ 2 - 4 * Real.sqrt 5 + 4 := by ring
        _ = 5 - 4 * Real.sqrt 5 + 4 := by rw [Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
        _ = 9 - 4 * Real.sqrt 5 := by ring
    have h6 : Real.sqrt 5 - 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
    rw [←h5]
    field_simp [Real.sqrt_sq h6]
  rw [h3, h4]
  <;> ring_nf <;> norm_num
  <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]