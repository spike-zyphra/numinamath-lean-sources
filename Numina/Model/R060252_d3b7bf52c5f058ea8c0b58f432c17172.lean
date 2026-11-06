import Mathlib

theorem number_theory_288635 : ∃ x : ℤ, x > Real.sqrt 11 ∧ x < Real.sqrt 19 := by
  use 4
  constructor
  · -- Prove that 4 > Real.sqrt 11
    have h1 : (4 : ℝ) > Real.sqrt 11 := by
      have h2 : Real.sqrt 11 < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> (norm_num)
      linarith
    exact_mod_cast h1
  · -- Prove that 4 < Real.sqrt 19
    have h3 : (4 : ℝ) < Real.sqrt 19 := by
      have h4 : (4 : ℝ) < Real.sqrt 19 := by
        rw [Real.lt_sqrt] <;> (norm_num)
      linarith
    exact_mod_cast h3