import Mathlib

theorem number_theory_206577 : ∃ n : ℕ, n > 1 ∧ ∃ k : ℕ, Real.sqrt (n * Real.sqrt (n * Real.sqrt n)) = k := by
  use 256
  constructor
  · norm_num
  · use 128
    have h1 : Real.sqrt (256 : ℝ) = 16 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((256 : ℝ) * Real.sqrt (256 : ℝ)) = 64 := by
      rw [h1]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((256 : ℝ) * Real.sqrt ((256 : ℝ) * Real.sqrt (256 : ℝ))) = (128 : ℝ) := by
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact_mod_cast h3