import Mathlib

theorem number_theory_99253 : ∃ n : ℕ, 1 < n ∧ ∃ k : ℕ, Real.sqrt (n * Real.sqrt (n * Real.sqrt n)) = k := by
  use 256
  constructor
  · norm_num
  · use 128
    have h1 : Real.sqrt (256 : ℝ) = (16 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((256 : ℝ) * Real.sqrt (256 : ℝ)) = (64 : ℝ) := by
      rw [h1]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (256 * Real.sqrt (256 * Real.sqrt (256 : ℝ))) = (128 : ℝ) := by
      have eq1 : Real.sqrt (256 : ℝ) = (16 : ℝ) := h1
      have eq2 : Real.sqrt ((256 : ℝ) * Real.sqrt (256 : ℝ)) = (64 : ℝ) := h2
      have eq4 : Real.sqrt (256 * Real.sqrt (256 * Real.sqrt (256 : ℝ))) =
          Real.sqrt (256 * (64 : ℝ)) := by
        have eq5 : Real.sqrt (256 * Real.sqrt (256 : ℝ)) = (64 : ℝ) := by
          linarith [eq2]
        have eq6 : (256 * Real.sqrt (256 * Real.sqrt (256 : ℝ)) : ℝ) = (256 * (64 : ℝ) : ℝ) := by 
          have eq7 : Real.sqrt (256 * Real.sqrt (256 : ℝ)) = (64 : ℝ) := eq5
          have eq8 : (256 * Real.sqrt (256 * Real.sqrt (256 : ℝ)) : ℝ) = (256 * (64 : ℝ) : ℝ) := by
            rw [eq7]
            <;> norm_num
          linarith [eq8]
        rw [eq6]
        all_goals norm_num
      have h4 : Real.sqrt (256 * (64 : ℝ)) = (128 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [eq4, h4]
    exact_mod_cast h3