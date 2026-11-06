import Mathlib

variable (x y z : ℝ)

def f (a b : ℝ) := a * b

theorem algebra_8744 {f : ℝ → ℝ → ℝ} (h : ∀ x y z, f x (f y z) = f x y + z)
    (h' : ∀ x, f x x = 0) : f 2000 2022 = -22 := by

  have eq1 : ∀ x y, f x y = f x 0 - y := by
    intro x y
    have h1 := h x y y
    have h2 : f y y = 0 := h' y
    simp [h2] at h1 
    linarith

  have eq2 : f 0 0 = 0 := by 
    specialize h' 0
    norm_num at h'
    linarith

  have eq3 : ∀ b, f 0 b = -b := by
    intro b
    have eq4 : f 0 b = f 0 0 - b := eq1 0 b
    rw [eq4]
    rw [eq2]
    all_goals
      ring

  have eq4 : f 2000 0 = 2000 := by 
    have h2 := h 0 2000 0
    have eq5 : f 0 (f 2000 0) = - (f 2000 0) := by 
      apply eq3
    have eq6 : f 0 2000 = -2000 := by 
      apply eq3
    simp [eq5, eq6] at h2 
    linarith

  have eq5 : f 2000 2022 = f 2000 0 - 2022 := by 
    specialize eq1 2000 2022
    simpa using eq1

  rw [eq5]
  rw [eq4]
  all_goals
    norm_num