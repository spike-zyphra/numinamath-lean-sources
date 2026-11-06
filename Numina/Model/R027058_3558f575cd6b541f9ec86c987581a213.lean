import Mathlib

theorem algebra_74361 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y + x * y)
    (h' : f 75 - f 51 = 1230) : f 100 = 3825 := by
  have h0 : f 0 = 0 := by 
    have h00 := h 0 0
    norm_num at h00
    linarith
  have eq1 : f 75 = 75 * f 1 + (74 * 75 / 2 : ℝ) := by 
    have eq2 : ∀ (n : ℕ), f ((↑n : ℝ)) = (↑n : ℝ) * f 1 + ((↑n - 1 : ℝ) * (↑n : ℝ) / 2 : ℝ) := by
      intro n 
      induction n with
      | zero =>
        simp [h0]
      | succ n ih =>
        have eq3 : f ((↑(n + 1 : ℕ) : ℝ)) = f ((↑n : ℝ) + 1) := by 
          simp at *
        rw [eq3]
        rw [h (↑n : ℝ) (1 : ℝ)]
        simp [ih]
        field_simp at *
        ring_nf 
    specialize eq2 75 
    norm_num at eq2 ⊢ 
    linarith 
  have eq2 : f 51 = 51 * f 1 + (50 * 51 / 2 : ℝ) := by 
    have eq2 : ∀ (n : ℕ), f ((↑n : ℝ)) = (↑n : ℝ) * f 1 + ((↑n - 1 : ℝ) * (↑n : ℝ) / 2 : ℝ) := by
      intro n 
      induction n with
      | zero =>
        simp [h0]
      | succ n ih =>
        have eq3 : f ((↑(n + 1 : ℕ) : ℝ)) = f ((↑n : ℝ) + 1) := by 
          simp at *
        rw [eq3]
        rw [h (↑n : ℝ) (1 : ℝ)]
        simp [ih]
        field_simp at *
        ring_nf
    specialize eq2 51 
    norm_num at eq2 ⊢ 
    linarith 
  have eq3 : f 1 = (-45 / 4 : ℝ) := by 
    rw [eq1, eq2] at h'
    linarith 
  have eq4 : f 100 = 100 * f 1 + (99 * 100 / 2 : ℝ) := by 
    have eq2 : ∀ (n : ℕ), f ((↑n : ℝ)) = (↑n : ℝ) * f 1 + ((↑n - 1 : ℝ) * (↑n : ℝ) / 2 : ℝ) := by 
      intro n 
      induction n with
      | zero =>
        simp [h0]
      | succ n ih =>
        have eq3 : f ((↑(n + 1 : ℕ) : ℝ)) = f ((↑n : ℝ) + 1) := by 
          simp at *
        rw [eq3]
        rw [h (↑n : ℝ) (1 : ℝ)]
        simp [ih]
        field_simp at *
        ring_nf 
    specialize eq2 100 
    norm_num at eq2 ⊢ 
    linarith 
  rw [eq4, eq3]
  norm_num