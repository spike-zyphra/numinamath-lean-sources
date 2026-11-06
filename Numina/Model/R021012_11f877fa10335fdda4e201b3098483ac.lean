import Mathlib

theorem algebra_228485 (x y z b : ℝ) (h₀ : 3 * x * y * z - x ^ 3 - y ^ 3 - z ^ 3 = b ^ 3)
    (h₁ : x + y + z = 2 * b) (h₂ : x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2) :
    (b = 0 ∧ (x = 0 ∧ y = 0 ∧ z = 0)) ∨ (b ≠ 0 ∧ False) := by
  have h3 : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  rw [h₁, h₂] at h3
  have h4 : b ^ 2 ≤ 0 := by 
    nlinarith 
  have hb : b = 0 := by
    nlinarith [sq_nonneg b]
  have hx : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
    rw [hb] at h₂
    nlinarith 
  have h4 : x ^ 2 ≥ 0 := sq_nonneg x
  have h5 : y ^ 2 ≥ 0 := sq_nonneg y
  have h6 : z ^ 2 ≥ 0 := sq_nonneg z
  have hx2 : x ^ 2 = 0 := by
    nlinarith
  have hy2 : y ^ 2 = 0 := by
    nlinarith
  have hz2 : z ^ 2 = 0 := by
    nlinarith
  have hx3 : x = 0 := by nlinarith
  have hy3 : y = 0 := by nlinarith
  have hz3 : z = 0 := by nlinarith
  left
  constructor
  · exact hb
  constructor
  · exact hx3
  constructor
  · exact hy3
  · exact hz3