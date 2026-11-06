import Mathlib

theorem number_theory_191716 (n : ℕ) : 9 ∣ 4^n + 15 * n - 1 := by
  have h1 : ∀ (n : ℕ), 9 ∣ 4^n + 15 * n - 1 := by 
    intro n 
    induction n with
    | zero =>
      norm_num 
    | succ n ih =>
      have h2 : (4 ^ (n + 1) + 15 * (n + 1) - 1 : ℕ) = (4 ^ n + 15 * n - 1 : ℕ) + (3 * (4 ^ n) + 15) := by 
        cases n with
        | zero =>
          all_goals 
            omega
        | succ n =>
          all_goals 
            simp [Nat.pow_add, Nat.mul_add]
            <;> ring_nf 
            <;> omega 
      rw [h2] 
      omega
  exact h1 n