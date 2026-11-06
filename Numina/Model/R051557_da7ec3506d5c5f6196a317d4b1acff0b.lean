import Mathlib

theorem number_theory_282912 {n : ℕ} (hn : n > 60) (h : 40 < (n - 60) * 2 ∧ (n - 60) * 2 < 100)
    (h1 : (n - 60) * 3 = (n - 60) * 2 + (n - 60) * 3 / 7) :
    n = 108 ∧ (n - 60) * 2 = 111 := by
  -- Extract the bounds from hypothesis h
  have h2 : 40 < (n - 60) * 2 := h.1
  have h3 : (n - 60) * 2 < 100 := h.2

  -- Calculate tight bounds for n - 60
  have h4 : 20 < n - 60 := by 
    omega

  have h5 : n - 60 < 50 := by
    omega

  -- Use omega to solve the constraints with the equation
  omega