import Mathlib

theorem algebra_242582 (f : ℕ → ℕ) (h : ∀ x y, 0 < x → 0 < y → f (x * y) = f x + f y)
    (h10 : f 10 = 14) (h40 : f 40 = 20) : f 500 = 39 := by 
  -- Compute f(4) using the fact that f(40) = f(4) + f(10).
  have f4 : f 4 = 6 := by 
    specialize h 4 10 (by norm_num) (by norm_num)
    norm_num [show f 40 = 20 by exact h40, show f 10 = 14 by exact h10] at h 
    omega
  -- Compute f(2) using the fact that f(4) = f(2) + f(2).
  have f2 : f 2 = 3 := by 
    specialize h 2 2 (by norm_num) (by norm_num)
    norm_num [f4] at h 
    omega
  -- Compute f(5) using the fact that f(10) = f(2) + f(5).
  have f5 : f 5 = 11 := by 
    specialize h 2 5 (by norm_num) (by norm_num)
    norm_num [h10, f2] at h 
    omega
  -- Compute f(50) using the fact that f(50) = f(10) + f(5).
  have h50 : f 50 = 25 := by 
    specialize h 10 5 (by norm_num) (by norm_num)
    norm_num [h10, f5] at h 
    omega
  -- Compute f(500) using the fact that f(500) = f(10) + f(50).
  specialize h 10 50 (by norm_num) (by norm_num)
  norm_num [h10, h50] at h 
  omega