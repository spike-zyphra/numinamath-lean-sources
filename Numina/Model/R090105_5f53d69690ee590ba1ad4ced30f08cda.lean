import Mathlib

/- For any product of five consecutive positive integers, if the product is necessarily a multiple of $p$, find the maximum possible value of $p$.

 -/
theorem number_theory_3623 (p : ℕ) (h : ∀ n > 0, p ∣ (n * (n + 1) * (n + 2) * (n + 3) * (n + 4))) :
    p ≤ 120 := by 
  have h1 := h 1 (by norm_num)
  norm_num at h1 ⊢
  have : p ≤ 120 := by 
    exact Nat.le_of_dvd (by norm_num) h1
  exact this