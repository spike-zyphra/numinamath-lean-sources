import Mathlib

theorem algebra_12300 : ¬ ∃ x : ℝ, abs (2 * x - 5) + abs (3 * x - 7) + abs (5 * x - 11) = 2015 / 2016 := by
  by_contra h
  rcases h with ⟨x, hx⟩
  by_cases h1 : 2 * x - 5 ≥ 0
  · -- Case 1: $2x - 5 \geq 0 \implies x \geq \frac{5}{2}$
    rw [abs_of_nonneg h1] at hx
    by_cases h2 : 3 * x - 7 ≥ 0
    · -- Subcase 1a: $3x - 7 \geq 0 \implies x \geq \frac{7}{3}$
      rw [abs_of_nonneg h2] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Subcase 1a1: $5x - 11 \geq 0 \implies x \geq \frac{11}{5}$
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Subcase 1a2: $5x - 11 < 0 \implies x < \frac{11}{5}$
        rw [abs_of_neg (lt_of_not_ge h3)] at hx
        linarith
    · -- Subcase 1b: $3x - 7 < 0 \implies x < \frac{7}{3}$
      rw [abs_of_neg (lt_of_not_ge h2)] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Subcase 1b1: $5x - 11 \geq 0 \implies x \geq \frac{11}{5}$
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Subcase 1b2: $5x - 11 < 0 \implies x < \frac{11}{5}$
        rw [abs_of_neg (lt_of_not_ge h3)] at hx
        linarith
  · -- Case 2: $2x - 5 < 0 \implies x < \frac{5}{2}$
    rw [abs_of_neg (lt_of_not_ge h1)] at hx
    by_cases h2 : 3 * x - 7 ≥ 0
    · -- Subcase 2a: $3x - 7 \geq 0 \implies x \geq \frac{7}{3}$
      rw [abs_of_nonneg h2] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Subcase 2a1: $5x - 11 \geq 0 \implies x \geq \frac{11}{5}$
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Subcase 2a2: $5x - 11 < 0 \implies x < \frac{11}{5}$
        rw [abs_of_neg (lt_of_not_ge h3)] at hx
        linarith
    · -- Subcase 2b: $3x - 7 < 0 \implies x < \frac{7}{3}$
      rw [abs_of_neg (lt_of_not_ge h2)] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Subcase 2b1: $5x - 11 \geq 0 \implies x \geq \frac{11}{5}$
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Subcase 2b2: $5x - 11 < 0 \implies x < \frac{11}{5}$
        rw [abs_of_neg (lt_of_not_ge h3)] at hx
        linarith