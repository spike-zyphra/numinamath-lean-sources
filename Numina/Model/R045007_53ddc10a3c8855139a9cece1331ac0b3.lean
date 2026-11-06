import Mathlib

open Real

theorem algebra_93533 {a : ℝ} {r : ℝ} (hr : -1 < r ∧ r < 1) :
    ∑' n : ℕ, a * r ^ n = a / (1 - r) ∧
    ∑' n : ℕ, (a * r ^ n) ^ 2 = a ^ 2 / (1 - r ^ 2) := by
  have h1 : -1 < r := hr.1
  have h2 : r < 1 := hr.2
  have hr_abs : abs r < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  constructor
  · -- Proof of the first part: $\sum_{n=0}^\infty a \cdot r^n = \frac{a}{1-r}$
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · exact hr_abs
  · -- Proof of the second part: $\sum_{n=0}^\infty (a \cdot r^n)^2 = \frac{a^2}{1-r^2}$
    have h3 : abs (r ^ 2) < 1 := by
      have h4 : (r ^ 2 : ℝ) < 1 := by nlinarith [sq_nonneg (r - 1), sq_nonneg (r + 1), h1, h2]
      have h5 : abs (r ^ 2) = r ^ 2 := by
        apply abs_of_nonneg
        nlinarith
      rw [h5]
      all_goals linarith
    have h4 : ∑' n : ℕ, (a * r ^ n) ^ 2 = ∑' n : ℕ, a ^ 2 * (r ^ 2) ^ n := by
      have h5 : ∀ n : ℕ, (a * r ^ n) ^ 2 = a ^ 2 * ((r ^ 2) ) ^ n := by
        intro n
        ring_nf
      simp_all [h5]
    rw [h4]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · -- The first term of the squared series is a^2
      ring
    · exact h3