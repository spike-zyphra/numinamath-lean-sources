import Mathlib

theorem algebra_121299 (f : ℝ → ℝ) (h : ∀ x, f (x + 2) + f (x - 2) = f x) :
    f (x + 12) = f x := by
  have eq1 : f (x + 2) = f x - f (x - 2) := by 
    have h1 := h x 
    ring_nf at h1 ⊢ 
    linarith 
  have eq2 : f (x + 4) = -f (x - 2) := by 
    have h1 := h (x + 2) 
    rw [show x + 2 + 2 = x + 4 by ring] at h1 
    rw [show x + 2 - 2 = x by ring] at h1 
    simp [eq1] at h1 ⊢ 
    all_goals linarith 
  have eq3 : f (x + 6) = -f x := by 
    have h1 := h (x + 4) 
    rw [show x + 4 + 2 = x + 6 by ring] at h1 
    rw [show x + 4 - 2 = x + 2 by ring] at h1 
    simp [eq2, eq1] at h1 ⊢ 
    all_goals linarith 
  have eq4 : f (x + 8) = -f (x + 2) := by 
    have h1 := h (x + 6) 
    rw [show x + 6 + 2 = x + 8 by ring] at h1 
    rw [show x + 6 - 2 = x + 4 by ring] at h1 
    simp [eq3, eq2] at h1 ⊢ 
    all_goals linarith 
  have eq5 : f (x + 10) = f (x - 2) := by 
    have h1 := h (x + 8) 
    rw [show x + 8 + 2 = x + 10 by ring] at h1 
    rw [show x + 8 - 2 = x + 6 by ring] at h1 
    simp [eq4, eq3] at h1 ⊢ 
    all_goals linarith 
  have eq6 : f (x + 12) = f x := by 
    have h1 := h (x + 10) 
    rw [show x + 10 + 2 = x + 12 by ring] at h1 
    rw [show x + 10 - 2 = x + 8 by ring] at h1 
    simp [eq5, eq4] at h1 ⊢ 
    all_goals linarith 
  linarith [eq6]