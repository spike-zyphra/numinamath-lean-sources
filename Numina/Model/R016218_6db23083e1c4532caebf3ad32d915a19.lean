import Mathlib

theorem algebra_146049 (α : ℝ) (n : ℕ) :
    (X ^ 2 + 1) ∣ (Real.cos α + X * Real.sin α) ^ n -
      Real.cos (n * α) - X * Real.sin (n * α) := by
  use ((Real.cos α + X * Real.sin α) ^ n - Real.cos (n * α) - X * Real.sin (n * α)) / (X ^ 2 + 1)
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> ring
  <;> norm_num
  <;> ring_nf
  <;> norm_num