import Mathlib

theorem number_theory_94105 (r : ℚ) (hr : r > 0) :
    -- The area of a circle with radius r is πr^2
    Irrational (Real.pi * r ^ 2) := by
  have h2 : Irrational (Real.pi) := by
    apply irrational_pi
  have h4 : r ^ 2 > (0 : ℚ) := by
    positivity
  have h3 : (r ^ 2 : ℝ) ≠ 0 := by
    have h4' : r ^ 2 > (0 : ℚ) := by
      positivity
    have h5 : r ^ 2 ≠ (0 : ℚ) := by
      linarith
    exact_mod_cast h5
  have h4' : (r ^ 2 : ℝ) = (r ^ 2 : ℚ) := by
    simp
  rw [h4']
  apply Irrational.mul_rat
  exact h2
  all_goals
    have h5 : (r ^ 2 : ℚ) ≠ 0 := by
      have h6 : (r ^ 2 : ℚ) > 0 := by
        positivity
      linarith
    exact h5