import Mathlib

theorem number_theory_235934 (a : ℕ → ℝ) (ha : ∀ n, a n = √(n ^ 2 + 1)) :
    ∃ n, Irrational (a n) := by 
  use 1
  have h1 : a 1 = √2 := by
    rw [ha 1]
    norm_num
  rw [h1]
  apply irrational_sqrt_two