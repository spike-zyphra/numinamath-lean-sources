import Mathlib

open Polynomial


theorem algebra_204344 (n : ℕ) :
    (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * n + 1) + X ^ (n + 2) := by
  have h1 : ∀ n : ℕ, (X ^ 2 + X + 1 : Polynomial ℤ) ∣ (X + 1) ^ (2 * n + 1) + X ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      use 1
      all_goals
        ring_nf
    | succ n ih =>
      rcases ih with ⟨q, hq⟩
      use (X + 1) ^ 2 * q - X ^ (n + 2)
      rw [show ((X + 1) ^ (2 * (n + 1) + 1) + X ^ ((n + 1) + 2) : Polynomial ℤ) =
          ((X + 1) ^ (2 * n + 1) + X ^ (n + 2) : Polynomial ℤ) * (X + 1) ^ 2 - (X ^ (n + 2) * (X ^ 2 + X + 1) : Polynomial ℤ) by
        ring_nf
      ]
      rw [hq]
      all_goals
        ring
  specialize h1 n
  simpa using h1