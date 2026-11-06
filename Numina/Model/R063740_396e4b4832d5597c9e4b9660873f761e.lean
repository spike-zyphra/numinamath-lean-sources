import Mathlib

theorem calculus_16972 : Complex.abs (12 - 9 * Complex.I) * Complex.abs (8 + 15 * Complex.I) = 255 := by
  have h₁ : Complex.abs (12 - 9 * Complex.I) = 15 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    -- Real.sqrt x = y iff y^2 = x and y ≥ 0
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h₂ : Complex.abs (8 + 15 * Complex.I) = 17 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    -- Real.sqrt x = y iff y^2 = x and y ≥ 0
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h₁, h₂]
  norm_num