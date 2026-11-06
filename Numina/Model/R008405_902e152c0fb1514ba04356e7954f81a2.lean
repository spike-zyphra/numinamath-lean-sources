import Mathlib

theorem number_theory_23348 {n : ℕ} 
    (hn₁ : 160 * n ≡ 1 [MOD 1399]) (hn₂ : n < 1399) :
    n = 1058 := by
  simp [Nat.ModEq] at hn₁ 
  omega