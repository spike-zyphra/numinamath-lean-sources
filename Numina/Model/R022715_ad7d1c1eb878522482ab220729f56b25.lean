import Mathlib

theorem number_theory_134270 {F : ℕ → ℤ} (hF : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) (n : ℕ) (hn : 1 ≤ n) :
    F (n - 1) * F (n + 1) - F n ^ 2 = (-1) ^ n := by 
  have h2 : ∀ (n : ℕ), 1 ≤ n → F (n - 1) * F (n + 1) - F n ^ 2 = (-1) ^ n := by
    intro n hn
    induction n with 
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with 
      | zero =>
        simp [hF0, hF1, hF] at ih ⊢
        all_goals linarith
      | succ n =>
        simp [hF0, hF1, hF, pow_two, pow_succ, pow_zero, mul_add, add_mul, sub_eq_add_neg, mul_sub, sub_mul] at ih ⊢ 
        all_goals
          ring_nf at ih ⊢
          linarith [ih]
  specialize h2 n hn 
  simpa using h2