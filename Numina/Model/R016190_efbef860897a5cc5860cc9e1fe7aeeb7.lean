import Mathlib

theorem algebra_241908 {b g : ℕ} (hb : b > 0) (hg : g > 0)
    (h1 : (2 * b : ℝ) / g = 3) (h2 : (3 * b + 8 * g : ℝ) / (g + 18 * b) = 29) :
    b + g = 5 := by
  have h1' : (g : ℝ) > (0 : ℝ) := by exact_mod_cast (show g > 0 by linarith)
  have h2' : (g + 18 * b : ℝ) > (0 : ℝ) := by
    positivity

  have eq1 : 2 * (b : ℝ) = 3 * (g : ℝ) := by
    have h11 : (g : ℝ) > 0 := by exact_mod_cast (show g > 0 by linarith)
    field_simp at h1
    linarith

  have eq1' : 2 * (b : ℕ) = 3 * (g : ℕ) := by
    exact_mod_cast eq1

  -- For the second equation
  have eq2 : (3 * (b : ℝ) + 8 * (g : ℝ)) = 29 * (g + 18 * (b : ℝ)) := by
    have h11 : (g + 18 * (b : ℝ)) > 0 := by positivity
    field_simp at h2
    linarith

  have eq3 : (b : ℝ) = (3 / 2 : ℝ) * (g : ℝ) := by
    linarith

  rw [show (b : ℝ) = (3 / 2 : ℝ) * (g : ℝ) by linarith [eq3] ] at eq2
  have eq4 : (g : ℝ) = (0 : ℝ) := by
    nlinarith

  have h3 : (g : ℝ) = (0 : ℝ) := eq4
  have h4 : (g : ℕ) = 0 := by
    exact_mod_cast h3

  linarith