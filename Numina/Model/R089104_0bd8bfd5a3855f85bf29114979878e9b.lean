import Mathlib

def a : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => a (n + 1) + a n

theorem number_theory_302760 (m : ℕ) (hm : 0 < m) :
    ∃ k, m ∣ a k ^ 4 - a k - 2 := by 
  -- use zero
  use 0
  -- simplify the terms
  simp [a, Nat.pow_succ, Nat.pow_zero, Nat.add_assoc]
  <;> omega