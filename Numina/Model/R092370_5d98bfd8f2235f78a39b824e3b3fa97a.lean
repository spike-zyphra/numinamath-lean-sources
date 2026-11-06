import Mathlib

theorem algebra_10301 (α : ℝ) (h : Real.sin (α - Real.pi / 3) = Real.sqrt 3 / 6) :
    Real.cos (2 * α - 2 * Real.pi / 3) = 5 / 6 := by
  have h1 : 2 * α - 2 * Real.pi / 3 = 2 * (α - Real.pi / 3) := by 
    ring
  rw [h1]
  have h2 : Real.cos (2 * (α - Real.pi / 3)) = 1 - 2 * (Real.sin (α - Real.pi / 3))^2 := by
    rw [Real.cos_two_mul]
    rw [Real.sin_sq]
    ring_nf
    <;> simp [Real.sin_sq]
    <;> ring_nf
  rw [h2, h]
  -- Compute (√3 / 6)² with field rules.
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  field_simp [show √3 ^ 2 = (3 : ℝ) by apply h3]
  <;> norm_num
  <;> try { assumption }
  <;> nlinarith [show √3 ^ 2 = (3 : ℝ) by apply Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  <;> ring_nf <;> norm_num