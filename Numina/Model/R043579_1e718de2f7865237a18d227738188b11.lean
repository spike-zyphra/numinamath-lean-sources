import Mathlib

theorem algebra_12774 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hf : ∀ x, f x = f (1 - x)) : f 2010 = 0 := by
  have h1 : f 0 = 0 := by
    have hodd0 : f (-0 : ℝ) = -f (0 : ℝ) := hodd 0
    simp at hodd0
    linarith

  have h4 : ∀ (n : ℕ), f ((↑n : ℝ) ) = 0 := by
    intro n
    induction n with
    | zero =>
      simpa using h1
    | succ n ih =>
      have eq1 : f ((↑(n + 1 : ℕ) : ℝ) ) = 0 := by
        have eq2 : f ((↑(n + 1 : ℕ) : ℝ) ) = f (1 - (↑(n + 1 : ℕ) : ℝ)) := by
          specialize hf ((↑(n + 1 : ℕ) : ℝ) )
          linarith
        have eq3 : (1 - (↑(n + 1 : ℕ) : ℝ) ) = (- (↑n : ℝ) ) := by
          simp at *
          <;> ring
        rw [eq3] at eq2
        have eq4 : f (- (↑n : ℝ) ) = - f ((↑n : ℝ) ) := by
          specialize hodd (↑n : ℝ)
          simpa using hodd
        have eq6 : f (- (↑n : ℝ) ) = 0 := by
          rw [eq4]
          rw [ih]
          all_goals norm_num
        linarith [eq2, eq6]
      simpa using eq1

  have h5 : f (2010 : ℝ) = 0 := by
    specialize h4 2010
    norm_num at h4 ⊢
    linarith
  exact h5