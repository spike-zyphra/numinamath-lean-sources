import Mathlib

theorem algebra_173566 {n : ℕ} (hn : n > 0) (h : ∃ x y, x > 0 ∧ y > 0 ∧ x + y = 12 ∧ x * (1 / 6 : ℝ) + y * (1 / 8 : ℝ) = n) :
    n = 7 := by
  rcases h with ⟨x, y, hx, hy, hxy, h1⟩
  have eq1 : (x + y : ℝ) = 12 := by
    exact_mod_cast hxy
  have eq2 : (x * (1 / 6 : ℝ) + y * (1 / 8 : ℝ) = (n : ℝ)) := by
    simpa using h1
  have eq3 : (y = (12 - x : ℝ)) := by
    linarith [eq1]
  rw [eq3] at eq2
  have eq4 : (x = (24 * (n : ℝ) - 36 : ℝ)) := by
    linarith 
  have h2 : (n : ℝ) > 1.5 := by
    nlinarith [show 0 < (x : ℝ) by linarith, eq4]
  have h3 : (n : ℝ) < (2 : ℝ) := by
    have hy : (y : ℝ) > 0 := by
      exact_mod_cast hy
    nlinarith [show 0 < (y : ℝ) by linarith, eq3, eq4]
  have h4 : n > 1 := by
    by_contra h4
    push_neg at h4
    have : n ≤ 1 := by linarith
    have h5 : (n : ℝ) ≤ (1 : ℝ) := by
      exact_mod_cast (show (n : ℝ) ≤ (1 : ℝ) by
        exact_mod_cast this
      )
    nlinarith
  have h5 : n < 2 := by
    by_contra h5
    push_neg at h5
    have : n ≥ 2 := by linarith
    have h6 : (n : ℝ) ≥ (2 : ℝ) := by
      exact_mod_cast (show (n : ℝ) ≥ (2 : ℝ) by
        exact_mod_cast this
      )
    nlinarith
  linarith