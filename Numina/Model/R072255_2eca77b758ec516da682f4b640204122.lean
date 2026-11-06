import Mathlib

open Real Set

theorem inequalities_5204 :
    {x : ℝ | abs x < abs (2 * x - 1)} = {x | x < 1 / 3 ∨ x > 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First, let's solve the inequality $|x| < |2x-1|$.
    intro h
    by_cases hx : x ≥ 0
    · -- Case where $x \geq 0$
      by_cases h2 : 2 * x - 1 ≥ 0
      · -- Case where $2x-1 \geq 0$ (i.e., $x \geq \frac{1}{2}$)
        rw [abs_of_nonneg hx, abs_of_nonneg h2] at h
        have h3 : x > 1 := by linarith
        right
        exact h3
      · -- Case where $2x-1 < 0$ (i.e., $0 \leq x < \frac{1}{2}$)
        rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge h2)] at h
        have h3 : x < 1 / 3 := by linarith
        left
        exact h3
    · -- Case where $x < 0$
      by_cases h2 : 2 * x - 1 ≥ 0
      · -- Case where $2x-1 \geq 0$ (impossible)
        rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg h2] at h
        linarith
      · -- Case where $2x-1 < 0$ (which is always true)
        rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge h2)] at h
        have h3 : x < 0 := by linarith
        have h4 : x < 1 / 3 := by linarith
        left
        exact h4
  · -- Now, let's prove the reverse direction.
    rintro (h | h)
    · -- Case where $x < 1/3$
      by_cases hx : x ≥ 0
      · -- Case where $0 \leq x < 1/3$
        by_cases h2 : 2 * x - 1 ≥ 0
        · -- Case where $2x-1 \geq 0$ (impossible)
          rw [abs_of_nonneg hx, abs_of_nonneg h2]
          linarith
        · -- Case where $2x-1 < 0$ (valid)
          rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge h2)]
          linarith
      · -- Case where $x < 0$
        by_cases h2 : 2 * x - 1 ≥ 0
        · -- Case where $2x-1 \geq 0$ (impossible)
          rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg h2]
          linarith
        · -- Case where $2x-1 < 0$ (valid)
          rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge h2)]
          linarith
    · -- Case where $x > 1$
      have hx : x > 1 := h
      have hx2 : 2 * x - 1 ≥ 0 := by linarith
      rw [abs_of_nonneg (show (x : ℝ) ≥ 0 by linarith), abs_of_nonneg hx2]
      linarith