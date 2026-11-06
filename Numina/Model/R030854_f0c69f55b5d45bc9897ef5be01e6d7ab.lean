import Mathlib

open Polynomial

theorem algebra_194356 (n : ℕ) (p q : Polynomial ℝ)
    (hp : p = (X + 1)^(2 * n + 1) + X^(n + 2))
    (hq : q = X^2 + X + 1):
    q ∣ p := by
  rw [hp, hq]
  have h2 : ∀ (n : ℕ), (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) + (X : Polynomial ℝ) ^ (n + 2)) := by
    intro n
    induction n with
    | zero =>
      use 1
      all_goals
        ring
    | succ n ih =>
      have h3 : (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * (n + 1) + 1) + (X : Polynomial ℝ) ^ ((n + 1) + 2)) := by
        have eq1 : ((X + 1 : Polynomial ℝ) ^ (2 * (n + 1) + 1) + (X : Polynomial ℝ) ^ ((n + 1) + 2)) =
            ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * (X ^ 2 + 2 * X + 1) + (X : Polynomial ℝ) ^ (n + 2) * X) := by
          ring_nf
        rw [eq1]
        have h4 : (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * (X ^ 2 + 2 * X + 1) + (X : Polynomial ℝ) ^ (n + 2) * X) := by
          have h5 : (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) + (X : Polynomial ℝ) ^ (n + 2)) := ih
          have h9 : (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * (X ^ 2 + X + 1)) := by
            use (X + 1 : Polynomial ℝ) ^ (2 * n + 1)
            all_goals ring
          have h12 : (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * X + (X : Polynomial ℝ) ^ (n + 2) * X) := by
            have h8 : ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * X + (X : Polynomial ℝ) ^ (n + 2) * X) = ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) + (X : Polynomial ℝ) ^ (n + 2)) * X := by 
              ring 
            rw [h8]
            obtain ⟨q, hq⟩ := h5
            use q * X
            all_goals 
              rw [hq]
              all_goals 
                ring
          have h16 : (X ^ 2 + X + 1 : Polynomial ℝ) ∣ ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * (X ^ 2 + X + 1) + ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * X + (X : Polynomial ℝ) ^ (n + 2) * X)) := by 
            apply dvd_add h9 h12
          have eq3 : ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * (X ^ 2 + 2 * X + 1) + (X : Polynomial ℝ) ^ (n + 2) * X) = 
              ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * (X ^ 2 + X + 1) + ((X + 1 : Polynomial ℝ) ^ (2 * n + 1) * X + (X : Polynomial ℝ) ^ (n + 2) * X)) := by 
            ring 
          rw [eq3]
          exact h16
        exact h4
      exact h3
  exact h2 n