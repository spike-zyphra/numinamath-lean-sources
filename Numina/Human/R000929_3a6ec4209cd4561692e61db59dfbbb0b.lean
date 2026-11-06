import Mathlib

/- Compute $997^{-1}$ modulo $1000$. Express your answer as an integer from $0$ to $999$. -/
theorem number_theory_19172 {n : ℕ} 
    (hn₁ : n ≤ 999) (hn₂ : 997 * n ≡ 1 [MOD 1000]) : 
    n = 333 := by 
  rw [Nat.ModEq] at hn₂
  omega