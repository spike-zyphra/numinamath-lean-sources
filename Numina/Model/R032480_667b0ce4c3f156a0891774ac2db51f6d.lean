import Mathlib

open Real

theorem inequalities_314883 :
    ¬∃ x y z : ℝ, |x| < |y - z| ∧ |y| < |z - x| ∧ |z| < |x - y| := by 
  rintro ⟨x, y, z, h₁, h₂, h₃⟩
  have h1' : x ^ 2 < (y - z) ^ 2 := by
    apply sq_lt_sq.mpr
    simpa using h₁
  have h2' : y ^ 2 < (z - x) ^ 2 := by
    apply sq_lt_sq.mpr 
    simpa using h₂
  have h3' : z ^ 2 < (x - y) ^ 2 := by
    apply sq_lt_sq.mpr 
    simpa using h₃ 
  have h4 : (y - z) ^ 2 = y ^ 2 + z ^ 2 - 2 * (y * z) := by ring 
  have h5 : (z - x) ^ 2 = z ^ 2 + x ^ 2 - 2 * (z * x) := by ring 
  have h6 : (x - y) ^ 2 = x ^ 2 + y ^ 2 - 2 * (x * y) := by ring 
  rw [h4] at h1'
  rw [h5] at h2'
  rw [h6] at h3'
  nlinarith [sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y), sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]