import Mathlib

theorem number_theory_255588 (n : ℕ) (a : ℤ)(ha : a ≠ 0): a^2 ∣ (a * n - 1) * (a + 1)^n + 1 := by 
  have h1 : ∀ (n : ℕ), a^2 ∣ (a * n - 1) * (a + 1)^n + 1 := by 
    intro n 
    induction n with 
    | zero =>
      use 0 
      all_goals 
        ring
    | succ n ih =>
      rcases ih with ⟨k, hk⟩
      use k + (↑n + 1) * (a + 1)^↑n 
      simp [pow_succ, mul_add, mul_sub, add_mul, sub_mul, mul_assoc] at hk ⊢ 
      ring_nf at hk ⊢ 
      <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_nonneg (a), sq_nonneg (a + 1)]
  specialize h1 n 
  simpa using h1