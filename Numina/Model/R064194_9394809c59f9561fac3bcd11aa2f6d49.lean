import Mathlib

open Nat

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_134530 :
    IsLeast {N | 10 ≤ S (S N)} 199 := by
  constructor
  · -- Show 199 is indeed in the set
    show 10 ≤ S (S 199)
    native_decide
  · -- Show there is no smaller element in the set
    intro N h
    have h1 : 10 ≤ S (S N) := by
      simpa using h
    by_contra h'
    push_neg at h'
    interval_cases N <;> norm_num [S] at h1 ⊢
    all_goals
      contradiction