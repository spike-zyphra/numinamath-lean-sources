import Mathlib

def s : ℕ → ℕ
| n => (Nat.digits 10 n).sum

def p : ℕ → ℕ
| n => (Nat.digits 10 n).prod

theorem number_theory_152403 :
    ∑ n in (Finset.Ico 1 100).filter (fun n => s n + p n = n), n = 531 := by 
  native_decide