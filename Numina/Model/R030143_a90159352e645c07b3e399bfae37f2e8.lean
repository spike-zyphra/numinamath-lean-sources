import Mathlib


theorem algebra_237625 (n : ℤ) :
    (16 * (n ^ 2 - n - 1) ^ 2) % (2 * n - 1) = 0 ↔
    n = -12 ∨ n = -2 ∨ n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 13 := by
  constructor
  · -- Assume $16(n^2 - n - 1)^2$ is divisible by $2n - 1$, prove $n \in \{-12, -2, 0, 1, 3, 13\}$.
    intro h
    have h1 : (2 * n - 1) ∣ 16 * (n ^ 2 - n - 1) ^ 2 := by
      have h2 : (16 * (n ^ 2 - n - 1) ^ 2) % (2 * n - 1) = 0 := h
      exact Int.dvd_of_emod_eq_zero h2
    have h2 : (2 * n - 1) ∣ 25 := by
      have h5 : (2 * n - 1) ∣ 16 * (n ^ 2 - n - 1) ^ 2 := h1
      have h7 : (2 * n - 1) ∣ (16 * (n ^ 2 - n - 1) ^ 2 - (2 * n - 1) * (8 * n ^ 3 - 12 * n ^ 2 - 14 * n + 9) : ℤ) := by
        apply Dvd.dvd.sub
        · exact h1
        · use (8 * n ^ 3 - 12 * n ^ 2 - 14 * n + 9)
          all_goals ring
      have h8 : (16 * (n ^ 2 - n - 1) ^ 2 - (2 * n - 1) * (8 * n ^ 3 - 12 * n ^ 2 - 14 * n + 9) : ℤ) = 25 := by
        nlinarith [sq_nonneg (n * 2 - 1), sq_nonneg (n ^ 2 - n - 1), sq_nonneg (n - 3), sq_nonneg (n + 12), sq_nonneg (n + 2), sq_nonneg (n - 13)]
      rw [h8] at h7
      exact h7
    -- From h2, (2n - 1) divides 25, so we can find all the possible (2n - 1)
    -- From which we can determine possible n.
    have h3 : (2 * n - 1) ∣ 25 := h2
    have h4 : (2 * n - 1) ≤ 25 := by
      apply Int.le_of_dvd (show 0 < (25 : ℤ) by norm_num) h3
    have h5 : (2 * n - 1) ≥ -25 := by
      have h6 : -(2 * n - 1) ∣ 25 := by
        exact Int.neg_dvd.2 h3
      have h7 : -(2 * n - 1) ≤ 25 := by
        apply Int.le_of_dvd (show 0 < (25 : ℤ) by norm_num) h6
      omega
    have h6 : n ≤ 13 := by
      omega
    have h7 : n ≥ -12 := by
      omega
    interval_cases n <;> tauto
  · -- Assume $n \in \{-12, -2, 0, 1, 3, 13\}$, prove $16(n^2 - n - 1)^2$ is divisible by $2n - 1$.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num