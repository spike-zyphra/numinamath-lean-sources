import Mathlib

theorem number_theory_1634 (n : ℕ) (hn : n > 0) : 7 ∣ 13^n + 6^(n-1) := by 
  induction n with 
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with 
    | zero =>
      -- base case n = 1: 13^1 + 6^0 = 13 + 1 = 14, which is divisible by 7.
      norm_num 
    | succ n =>
      -- induction step: assume true for n = k, prove for n = k + 1
      simp [pow_succ, pow_succ] at ih ⊢ 
      <;> norm_num [pow_succ, pow_succ] at ih ⊢ 
      <;> omega