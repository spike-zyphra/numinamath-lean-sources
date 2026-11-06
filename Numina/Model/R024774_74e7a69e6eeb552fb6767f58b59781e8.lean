import Mathlib

theorem algebra_11461 : Complex.abs (2 - 4 * .I) + Complex.abs (2 + 4 * .I) = 4 * Real.sqrt 5 := by
  have h1 : Complex.abs (2 - 4 * Complex.I) = Real.sqrt 20 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  have h2 : Complex.abs (2 + 4 * Complex.I) = Real.sqrt 20 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
  rw [h1, h2]
  have h3 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h3]
  ring_nf
  <;> norm_num