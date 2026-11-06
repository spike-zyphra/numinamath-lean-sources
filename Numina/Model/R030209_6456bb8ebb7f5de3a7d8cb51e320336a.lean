import Mathlib


theorem algebra_235001 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) = f x * f y - f (x + y) + 1)
    (h1 : f 1 = 2) (m : ℤ) : f m = m + 1 := by

  have f0 : f 0 = 1 := by
    have h00 := h 0 0
    norm_num at h00
    have h2 : (f 0 - 1) ^ 2 = 0 := by nlinarith
    have : f 0 - 1 = 0 := by
      apply pow_eq_zero 
      exact h2
    linarith

  have f10 : ∀ x : ℝ, f (x + 1) = f x + 1 := by
    intro x
    have eq1 : f (x * 1) = f x * f 1 - f (x + 1) + 1 := by
      apply h
    rw [show x * 1 = x by ring, h1] at eq1
    linarith [eq1]

  have h20 : ∀ (n : ℤ), f ((↑n : ℝ)) = (↑n : ℝ) + 1 := by
    intro n
    induction n using Int.induction_on with
    | hz =>
      norm_num [f0]
    | hp n ih =>
      have eq3 : f ((↑(n + 1 : ℤ) : ℝ)) = f ((↑(n : ℤ) : ℝ) + 1) := by
        simp at *
      rw [eq3]
      rw [f10]
      rw [ih]
      all_goals simp at *
    | hn n ih =>
      have eq3 : f ((↑(-n - 1 : ℤ) : ℝ)) = f ((↑(-n : ℤ) : ℝ) - 1) := by
        simp at *
        all_goals ring_nf
      rw [eq3]
      have eq4 : f ((↑(-n : ℤ) : ℝ) - 1) = f ( (↑(-n : ℤ) : ℝ) ) - 1 := by
        have eq6 : f (((↑(-n : ℤ) : ℝ) - 1) * 1) = f ((↑(-n : ℤ) : ℝ) - 1) * f 1 - f (((↑(-n : ℤ) : ℝ) - 1) + 1) + 1 := by
          apply h
        have eq7 : ((↑(-n : ℤ) : ℝ) - 1) * 1 = (↑(-n : ℤ) : ℝ) - 1 := by ring
        rw [eq7] at eq6
        have eq8 : ((↑(-n : ℤ) : ℝ) - 1) + 1 = (↑(-n : ℤ) : ℝ) := by ring
        rw [eq8] at eq6
        rw [h1] at eq6
        nlinarith
      rw [eq4]
      rw [ih]
      all_goals simp at *
  
  specialize h20 m
  simpa using h20