import Mathlib

theorem algebra_181496 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 6 * (a + b - d) = 1)
    (h₂ : 5 * (a + c - d) = 1)
    (h₃ : 4 * (b + c - d) = 1)
    (h₄ : 3 * (a + b + c - d) = 1) :
    1 / (a + b + c) = 2 + 14/23 := by
  have eq1 : a + b - d = 1 / 6 := by
    linarith
  have eq2 : a + c - d = 1 / 5 := by
    linarith 
  have eq3 : b + c - d = 1 / 4 := by
    linarith
  have eq4 : a + b + c - d = 1 / 3 := by
    linarith  
  have eq5 : 2 * (a + b + c) - 3 * d = 37 / 60 := by 
    have h1 : a + b - d = 1 / 6 := eq1
    have h2 : a + c - d = 1 / 5 := eq2
    have h3 : b + c - d = 1 / 4 := eq3
    linarith
  have eq6 : a + b + c = 1 / 3 + d := by linarith [eq4]
  have h5 : d = 1 / 20 := by
    rw [eq6] at eq5
    linarith
  have h6 : a + b + c = 23 / 60 := by
    rw [h5] at eq6
    linarith
  have h7 : 1 / (a + b + c) = 60 / 23 := by
    rw [h6]
    norm_num
  rw [h7]
  all_goals norm_num