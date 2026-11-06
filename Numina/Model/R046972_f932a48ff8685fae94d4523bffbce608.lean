import Mathlib

theorem algebra_104699 (n : ℕ) :
    (X^2 + X + 1 : Polynomial ℤ) ∣ (X + 1)^(2*n + 1) + X^(n + 2) := by 
  have h1 : ∀ (n : ℕ), (X^2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * n + 1) + X ^ (n + 2) := by 
    intro n 
    induction n with 
    | zero => 
      use 1 
      all_goals 
        ring 
    | succ n ih =>
      have h2 : (X^2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * (n + 1) + 1) + X ^ ((n + 1) + 2) := by 
        have eq1 : (X + 1) ^ (2 * (n + 1) + 1) + X ^ ((n + 1) + 2) =
          ((X + 1) ^ (2 * n + 1) * (X ^ 2 + 2 * X + 1)) + (X ^ (n + 2) * X) := by 
          ring_nf
        rw [eq1]
        have eq2 : ((X + 1) ^ (2 * n + 1) * (X ^ 2 + 2 * X + 1)) + (X ^ (n + 2) * X) =
          ((X ^ 2 + X + 1) * ((X + 1) ^ (2 * n + 1)) ) + X * ((X + 1) ^ (2 * n + 1) + X ^ (n + 2)) := by
          ring_nf
        rw [eq2]
        have h3 : (X^2 + X + 1 : Polynomial ℤ) ∣ ((X ^ 2 + X + 1) * ((X + 1) ^ (2 * n + 1)) ) := by 
          use ((X + 1) ^ (2 * n + 1))
          all_goals ring 
        have h4 : (X^2 + X + 1 : Polynomial ℤ) ∣ X * ((X + 1) ^ (2 * n + 1) + X ^ (n + 2)) := by 
          have h5 : (X^2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * n + 1) + X ^ (n + 2) := ih
          have h6 : (X^2 + X + 1 : Polynomial ℤ) ∣ X * ((X + 1) ^ (2 * n + 1) + X ^ (n + 2)) := by
            exact dvd_trans h5 (by simp)
          exact h6 
        apply dvd_add h3 h4 
      simpa using h2 
  specialize h1 n
  simpa using h1