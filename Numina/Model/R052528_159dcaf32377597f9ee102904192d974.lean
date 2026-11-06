import Mathlib

def q : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_263093 : q (q (q (2000^2000))) = 4 := by 
  native_decide