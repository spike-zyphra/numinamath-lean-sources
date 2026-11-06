import Mathlib

theorem number_theory_116040 (n : ℕ) : 133 ∣ 11^(n + 2) + 12^(2 * n + 1) := by
  have h1 : ∀ (n : ℕ), 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
    intro n 
    induction n with
    | zero => 
      norm_num 
    | succ n ih => 
      have h2 : 133 ∣ 11 ^ (n + 1 + 2) + 12 ^ (2 * (n + 1) + 1) := by 
        have h3 : 11 ^ (n + 1 + 2) + 12 ^ (2 * (n + 1) + 1) = 11 * (11 ^ (n + 2)) + 144 * (12 ^ (2 * n + 1)) := by 
          ring_nf 
        rw [h3] 
        omega 
      exact h2 
  specialize h1 n 
  exact h1