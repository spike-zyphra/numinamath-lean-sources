import Mathlib

theorem algebra_326155 (f : ℕ → ℕ) (h₀ : ∀ n, 0 < n → 0 < f n)
    (h₁ : ∀ n m, 0 < n → 0 < m → f (f n + f m) = n + n) :
    f 1938 = 1938 := by
  have h3 : f 1938 > 0 := h₀ 1938 (by norm_num)
  have eq1 := h₁ 1938 (f 1938) (by norm_num) (h3)
  have eq2 := h₁ (f 1938) 1938 (h3) (by norm_num)
  have eq4 : (f 1938 + f 1938) = 1938 + 1938 := by 
    have eq5 : f (f 1938 + f (f 1938)) = f (f (f 1938) + f 1938) := by 
      have eq3 : f 1938 + f (f 1938) = f (f 1938) + f 1938 := by 
        omega 
      rw [eq3] 
      all_goals tauto 
    have eq6 : f (f 1938 + f (f 1938)) = 1938 + 1938 := by 
      simpa using eq1 
    have eq7 : f (f (f 1938) + f 1938) = (f 1938 + f 1938) := by 
      simpa using eq2 
    omega 
  have eq9 : 2 * f 1938 = 3876 := by 
    omega 
  have eq10 : f 1938 = 1938 := by 
    omega 
  exact eq10