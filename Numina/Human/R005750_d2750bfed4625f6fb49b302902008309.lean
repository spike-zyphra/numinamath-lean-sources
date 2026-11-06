import Mathlib
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Factorial.Basic

def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 1) => (a n).factorial + 1

theorem number_theory_609730 :
-- 存在最小的n使得a_n > 10^10
  ∃ n : ℕ+, (∀ k : ℕ, k < n → a k ≤ 10^10) ∧ a n > 10^10 := by
  use 6
  have a0 : a 0 = 0 := by rfl
  have a1 : a 1 = 1 := by rfl
  have a2 : a 2 = 2 := by rfl
  have a3 : a 3 = 3 := by rfl
  have a4 : a 4 = 7 := by rfl
  have a5 : a 5 = 5041 := by rfl
  have a6 : a 6 > 10^10 := by native_decide
  constructor
  intro k hk
  have h1: k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by 
    have hk_le_5 : k ≤ 5 := Nat.lt_succ.mp hk
    interval_cases k
    left; rfl
    right;left; rfl
    right;right;left;rfl
    right;right;right;left;rfl
    right;right;right;right;left;rfl
    right;right;right;right;right;rfl
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1)
  all_goals simp [a0,a1,a2,a3,a4,a5]
  rw[h1]
  linarith
  rw[h1]
  linarith
  rw[h1]
  linarith
  rw[h1]
  linarith
  rw[h1]
  linarith
  rw[h1]
  linarith
  omega
  


