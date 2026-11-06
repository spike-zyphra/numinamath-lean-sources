import Mathlib

theorem algebra_1822 (n : ℕ) : (3^(n+4) - 9 * (3^(n+1)) : ℝ) / (9 * 3^(n+2)) = 2 / 3 := by

  have h1 : (3 ^ (n + 4) - 9 * (3 ^ (n + 1)) : ℝ) = (18 * (3 : ℝ) ^ (n + 1) : ℝ) := by
    ring_nf
    <;> simp [pow_add]
    <;> ring_nf
    <;> norm_num

  have h2 : (9 * (3 : ℝ) ^ (n + 2) : ℝ) = (27 * (3 : ℝ) ^ (n + 1) : ℝ) := by
    ring_nf
    <;> simp [pow_add]
    <;> ring_nf
    <;> norm_num
  
  rw [h1, h2]

  have h3 : ((3 : ℝ) ^ (n + 1) : ℝ) ≠ 0 := by
    have h4 : (3 : ℝ) > 0 := by norm_num
    have h5 : ((3 : ℝ) ^ (n + 1) : ℝ) > 0 := by positivity 
    linarith

  field_simp [h3]
  <;> ring_nf
  <;> norm_num