import Mathlib

theorem number_theory_169530 :
    ∃ n : ℕ, 1 < n ∧ ∃ k : ℕ, Real.sqrt (n * Real.sqrt (n * Real.sqrt n)) = k := by
  use 256
  constructor
  · norm_num
  · -- Show that sqrt(256 * sqrt(256 * sqrt(256))) = 128
    use 128
    have h4' : Real.sqrt ((↑256) * Real.sqrt ((↑256) * Real.sqrt (↑256))) = (↑128 : ℝ) := by 
      have h1 : Real.sqrt (256 : ℝ) = 16 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt ((256 : ℝ) * Real.sqrt (256 : ℝ)) = 64 := by
        have h3 : Real.sqrt (256 : ℝ) = 16 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h3]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3' : Real.sqrt ((256 : ℝ) * Real.sqrt ((256 : ℝ) * Real.sqrt (256 : ℝ))) = (128 : ℝ) := by
        rw [h2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      simpa using h3'
    exact_mod_cast h4'