import Mathlib

theorem number_theory_276068 (n : ℕ) (hn : 0 < n) :
    133 ∣ 11^(n + 2) + 12^(2 * n + 1) := by
  induction n with 
  | zero => 
    exfalso
    linarith
  | succ k ih => 
    cases k with
    | zero => 
      norm_num
    | succ k => 
      norm_num [pow_succ, pow_mul] at ih ⊢
      <;> omega