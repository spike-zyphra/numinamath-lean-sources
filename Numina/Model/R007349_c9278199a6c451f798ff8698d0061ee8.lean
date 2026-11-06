import Mathlib

theorem algebra_22252 (A B C : ℝ × ℝ) (S : ℝ) (hΔ : ¬ ∃ t : ℝ, B - A = t • (C - A))
    (h₀ : A.1 + B.1 + C.1 = Real.sqrt 13) 
    (hS : S = (A.1 + B.1) / 2 + (B.1 + C.1) / 2 + (A.1 + C.1) / 2) :
    S ^ 2 = 13 := by 
  have h1 : S = A.1 + B.1 + C.1 := by 
    rw [hS]
    ring
  have h2 : S = Real.sqrt 13 := by 
    rw [h1]
    linarith [h₀]
  rw [h2]
  have h3 : (Real.sqrt 13 : ℝ) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  exact h3