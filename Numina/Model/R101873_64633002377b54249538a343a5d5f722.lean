import Mathlib

theorem number_theory_229337 : ¬(∃ x : ℤ, (2014 / 4 : ℝ) = x) := by 
  rintro ⟨x, hx⟩
  have h1 : (2014 : ℝ) / (4 : ℝ) = (x : ℝ) := by 
    simpa using hx
  have h3 : 4 * (x : ℝ) = (2014 : ℝ) := by
    linarith [h1]
  have h4 : 4 * x = 2014 := by
    exact_mod_cast h3
  omega