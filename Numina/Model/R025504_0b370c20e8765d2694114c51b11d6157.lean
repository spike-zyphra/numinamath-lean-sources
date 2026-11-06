import Mathlib

theorem algebra_600863 :
    ∃ f : ℤ → ℤ → ℤ,
      (∀ n m, f n m = (f (n - 1) m + f (n + 1) m + f n (m - 1) + f n (m + 1)) / 4) ∧
      (∀ k, ∃ m n, f m n > k ∧ ∃ m n, f m n < k) := by
  use fun n m => n^2 - m^2
  constructor
  · -- Show that the function satisfies the recurrence relation
    intro n m
    have h1 : (n - 1)^2 - m^2 + ((n + 1) ^ 2 - m^2) + (n ^ 2 - (m - 1)^2) + (n^2 - (m + 1)^2) = 4 * (n^2 - m^2) := by
      ring
    have h3 : ((n - 1) ^ 2 - m^2 + ((n + 1) ^ 2 - m^2) + (n ^ 2 - (m - 1)^2) + (n^2 - (m + 1)^2)) / 4 = n^2 - m^2 := by
      rw [show (n - 1) ^ 2 - m^2 + ((n + 1 : ℤ) ^ 2 - m^2) + (n ^ 2 - (m - 1) ^ 2) + (n ^ 2 - (m + 1) ^ 2) = 4 * (n ^2 - m^2) by linarith [h1] ]
      all_goals
        omega
    rw [h3]
    all_goals
      omega
  · -- Show that for all integer k, there are integers m, n s.t. f(m, n) > k and f(m, n) < k.
    intro k
    by_cases h1 : k < -3
    · -- Case k < -3
      use k + 1, k + 2
      constructor
      · -- Show that f(k + 1, k + 2) > k
        nlinarith
      · -- Show that exists m, n, f m n < k
        use k + 1, 2*k + 2
        all_goals
          nlinarith [sq_nonneg (k + 1), sq_nonneg (k + 2)]
    · -- Case k ≥ -3
      use k + 1, 0
      constructor
      · -- Show that f(k + 1, 0) > k
        nlinarith [sq_nonneg (k + 1)]
      · -- Show that exists m, n, f m n < k
        use 0, 2
        all_goals
          nlinarith