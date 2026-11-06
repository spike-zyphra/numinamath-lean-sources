import Mathlib

open Real

/- 13. Given the sequence $\{\sqrt[n]{n}\}\left(n \in \mathbf{Z}_{+}\right)$. Then the value of the largest term in the sequence is $\qquad$ . -/
theorem algebra_318299 (a : ℕ → ℝ) (ha : ∀ n, a n = (n : ℝ) ^ (1 / n : ℝ)) :
    IsGreatest {a n | n > 0} (3 ^ (1 / 3 : ℝ)) := by
  constructor
  . use 3
    simp [ha]
  . -- We prove that n ^ (1 / n) ≤ 3 ^ (1 / 3) for all n > 0.
    rintro _ ⟨n, hn, rfl⟩
    simp [ha]
    -- We cancel the nth root on both sides.
    rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (show 0 < (3 * n : ℝ) by positivity)]
    rw [← Real.rpow_mul (by simp), ← Real.rpow_mul (by simp)]
    field_simp
    -- Cast to natural numbers.
    norm_cast
    -- Now the goal reads `n ^ 3 ≤ 3 ^ n`.
    -- We check the cases n = 1, 2.
    rcases lt_or_le n 3 with hn' | hn'
    . interval_cases n <;> norm_num
    clear hn
    -- We prove for n ≥ 3 by induction.
    induction n, hn' using Nat.le_induction with
    | base =>
      simp
    | succ n hn' ih =>
      -- By the induction hypothesis, we only need to prove that
      -- (n + 1) ^ 3 ≤ 3 * n ^ 3.
      -- So knowing 3 ^ 3 * (n + 1) ^ 3 ≤ 3 * 4 ^ 3 * n ^ 3 proves more. (4 ^ 3 ≤ 3 * 3 ^ 3)
      suffices 3 ^ 3 * (n + 1) ^ 3 ≤ 4 ^ 3 * n ^ 3 by omega
      rw [← mul_pow, ← mul_pow]
      -- The power of 3 is the same on both sides, so we can cancel it.
      refine Nat.pow_le_pow_left ?_ 3
      omega
