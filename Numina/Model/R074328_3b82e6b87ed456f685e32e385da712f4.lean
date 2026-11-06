import Mathlib

theorem number_theory_281839 (n : ℕ) : 6 ∣ 2 * n^3 + 9 * n^2 + 13 * n := by
  have h1 : ∀ n : ℕ, 6 ∣ 2 * n^3 + 9 * n^2 + 13 * n := by 
    intro n 
    induction n with 
    | zero =>
      use 0 
      all_goals simp
    | succ k ih =>
      have eq1 : 2 * (k + 1)^3 + 9 * (k + 1)^2 + 13 * (k + 1) = (2 * k^3 + 9 * k^2 + 13 * k) + 6 * (k^2 + 4 * k + 4) := by 
        ring_nf 
      rw [eq1] at *
      omega 
  exact h1 n