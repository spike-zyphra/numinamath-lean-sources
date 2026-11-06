import Mathlib

/- Notice that  \[35\cdot40=1400.\]Find some integer $n$ with $0\leq n<1399$ such that $n$ is the multiplicative inverse to 160 modulo 1399. -/
theorem number_theory_23348 {n : ℕ} 
    (hn₁ : 160 * n ≡ 1 [MOD 1399]) (hn₂ : n < 1399) :
    n = 1058 := by 
  rw [Nat.ModEq] at hn₁
  omega