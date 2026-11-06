import Mathlib


/- Let $a_n=6^{n}+8^{n}$. Determine the remainder upon dividing $a_ {83}$ by $49$.
 -/
theorem number_theory_13327 {a : ℕ → ℕ} (ha : ∀ n, a n = 6^n + 8^n): a 83 % 49 = 35 := by 
  simp [ha]
