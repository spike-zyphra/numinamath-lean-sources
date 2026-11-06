import Mathlib

theorem number_theory_277960 {n : ℕ} :
  let num := (5 * 10^n - 1) * 10^(n+1) + 1
  let square1 := (5 * 10^n - 1)^2
  let square2 := (10^(n+1) - 1)^2
  num^2 = square1 * 10^(2*n+2) + square2 := by
  have eq1 : ∀ (n : ℕ),
    ((5 * 10^n - 1) * 10^(n+1) + 1) ^ 2 = (5 * 10^n - 1)^2 * 10^(2*n+2) + (10^(n+1) - 1)^2 := by
    intro n 
    induction n with
    | zero =>
      norm_num 
    | succ n ih =>
      simp [pow_succ, pow_zero, mul_add, add_mul, Nat.mul_sub, Nat.sub_mul, 
        mul_add, mul_comm, mul_assoc] at ih ⊢ 
      <;> ring_nf at ih ⊢ 
      <;> all_goals
        try { 
          omega 
        }
        <;> norm_num at ih ⊢ 
      all_goals
        nlinarith [pow_pos (by norm_num : (10 : ℕ) > 0) n, pow_pos (by norm_num : (10 : ℕ) > 0) (n + 1)]
  simpa [eq1] using eq1 n