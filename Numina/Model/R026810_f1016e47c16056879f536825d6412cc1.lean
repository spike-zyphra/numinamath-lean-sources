import Mathlib

theorem number_theory_51605 (a : ℕ → ℤ) (ha1 : Odd (a 1))
    (han : ∀ n > 0, n * (a (n + 1) - a n + 3) = a (n + 1) + a n + 3)
    (h2010 : 2010 ∣ a 2009) :
    IsLeast {n | 2 ≤ n ∧ 2010 ∣ a n} 671 := by

  have eq1 := han 1 (by norm_num)
  simp at eq1
  have h1 : a 1 = 0 := by
    omega
  
  rw [h1] at ha1
  rcases ha1 with ⟨k, hk⟩
  omega