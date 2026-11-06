import Mathlib

open Nat

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_8034 (n : ℕ) (h : 0 < n) :
    9 ∣ n ↔ 9 ∣ S n := by
  have h1 : n % 9 = (S n) % 9 := by 
    rw [show S n = (Nat.digits 10 n).sum by rfl]
    rw [Nat.modEq_nine_digits_sum (n)]
    all_goals try omega
  have h2 : 9 ∣ n ↔ n % 9 = 0 := by 
    omega
  have h3 : 9 ∣ S n ↔ (S n) % 9 = 0 := by
    omega
  rw [h2, h3]
  omega