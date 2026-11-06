import Mathlib
theorem algebra_609153 : IsGreatest {t : ℝ | ∀ a b c d : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * b + t * b * c + c * d} (3 / 2):= by
  constructor
  · -- First case, we need to show 3/2 is in the set.
    intro a b c d
    nlinarith [sq_nonneg (a - b / 2), sq_nonneg (d - c / 2), sq_nonneg (b - c), sq_nonneg (a - d), 
      sq_nonneg (b + c - 2 * a), sq_nonneg (b + c - 2 * d), 
      sq_nonneg (a - d + b - c), sq_nonneg (a + d - (b + c)), 
      sq_nonneg ((b - c) - (a - d))
    ]
  · -- Now, we need to prove maximality of 3/2.
    intro t ht
    have h1 := ht 1 2 2 1
    nlinarith