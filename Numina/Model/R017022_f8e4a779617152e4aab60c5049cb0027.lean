import Mathlib

theorem algebra_101307 (n : ℕ) (hn : n > 0) :
    (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * n + 1) + X ^ (n + 2) := by
  have h2 : ∀ n : ℕ, (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * n + 1) + X ^ (n + 2) := by
    intro n
    induction n with 
    | zero =>
      use 1 
      all_goals 
        ring
    | succ n ih =>
      have eq1 : ((X + 1 : Polynomial ℤ) ^ (2 * (n + 1) + 1) + (X : Polynomial ℤ) ^ ((n + 1) + 2)) = 
        (X + 1 : Polynomial ℤ) ^ (2 * n + 1) * (X ^ 2 + X + 1) + (X : Polynomial ℤ) * ((X + 1 : Polynomial ℤ) ^ (2 * n + 1) + (X : Polynomial ℤ) ^ (n + 2)) := by 
        ring
      rw [eq1]
      apply Dvd.dvd.add 
      · -- First term is divisible by X ^ 2 + X + 1 
        use (X + 1 : Polynomial ℤ) ^ (2 * n + 1) 
        all_goals 
          ring 
      · -- Second term is divisible by X ^ 2 + X + 1 
        have h3 : (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X : Polynomial ℤ) * ((X + 1 : Polynomial ℤ) ^ (2 * n + 1) + (X : Polynomial ℤ) ^ (n + 2) ) := by 
          have h4 : (X ^ 2 + X + 1 : Polynomial ℤ) ∣ ((X + 1 : Polynomial ℤ) ^ (2 * n + 1) + (X : Polynomial ℤ) ^ (n + 2) ) := by 
            exact ih 
          have h5 : (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X : Polynomial ℤ) * ((X + 1 : Polynomial ℤ) ^ (2 * n + 1) + (X : Polynomial ℤ) ^ (n + 2) ) := by 
            apply Dvd.dvd.mul_left 
            exact h4 
          exact h5 
        exact h3 
  apply h2 n