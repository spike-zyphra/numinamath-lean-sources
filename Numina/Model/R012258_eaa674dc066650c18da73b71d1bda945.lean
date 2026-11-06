import Mathlib
theorem number_theory_608111 (a : ℕ) (ha : ∀ n : ℕ, ∃ d : ℕ, d > 1 ∧ d ∣ n ^ 2 * a - 1 ∧ d ≡ 1 [MOD n]) : IsSquare a:= by 
  have h1 := ha 0
  rcases h1 with ⟨d, h2, h3, h4⟩
  simp [Nat.ModEq] at h4
  all_goals 
    omega