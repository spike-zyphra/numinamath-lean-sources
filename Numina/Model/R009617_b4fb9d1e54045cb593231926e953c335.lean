import Mathlib

theorem algebra_13055 {f g h : ℝ → ℝ}
    (hf : ∀ x, f x = 2 * x + 5)
    (hg : ∀ x, g x = Real.sqrt (f x) - 2)
    (hh : ∀ x, h x = f (g x)) :
    h 2 = 7 := by
  have f2 : f 2 = 9 := by
    rw [hf]
    norm_num
  have g2 : g 2 = Real.sqrt 9 - 2 := by 
    rw [hg]
    rw [f2]
  have sqrt9 : Real.sqrt 9 = 3 := by 
    rw [Real.sqrt_eq_cases]
    norm_num
  have g2' : g 2 = 1 := by 
    rw [g2, sqrt9]
    norm_num
  have f1 : f 1 = 7 := by 
    rw [hf]
    norm_num
  calc 
    h 2 = f (g 2) := by rw [hh]
    _ = f 1 := by rw [g2']
    _ = 7 := by exact f1