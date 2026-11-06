import Mathlib

theorem number_theory_853 (n : ℕ) (h₀ : 0 < n) : 9 ∣ 5^(2*n) - 6*n + 8 := by
  have h1 : ∀ (n : ℕ), 0 < n → 9 ∣ 5 ^ (2 * n) - 6 * n + 8 := by
    intro n hn
    induction n with
    | zero =>
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num at *
      | succ n =>
        simp [pow_mul, pow_add] at ih ⊢
        all_goals ring_nf at ih ⊢
        all_goals omega
  exact h1 n h₀