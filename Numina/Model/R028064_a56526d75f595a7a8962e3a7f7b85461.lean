import Mathlib

/- No matter what value $x$ takes, $\left|  x-2\right|  +\left|  x-5\right|  \geq a$ always holds, then the range of values for $a$ is ___          ___. -/
theorem inequalities_8232 (a : ℝ) :
    (∀ x : ℝ, |x - 2| + |x - 5| ≥ a) ↔ a ≤ 3 := by
  constructor
  · -- Forward: if $∀ x, |x - 2| + |x - 5| ≥ a$, then $a ≤ 3$
    intro h
    have h2 := h 2
    norm_num [abs] at h2 ⊢
    linarith
  · -- Backward: if $a ≤ 3$, then $∀ x, |x - 2| + |x - 5| ≥ a$
    intro ha x
    by_cases h1 : x ≥ 5
    · -- Case 1: x ≥ 5
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      all_goals
        linarith
    by_cases h2 : x ≥ 2
    · -- Case 2: 2 ≤ x < 5
      by_cases h3 : x < 5
      · -- Subcase 2a: 2 ≤ x < 5
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        all_goals
          linarith
      · -- Case 2b: x ≥ 5 (already covered)
        exfalso
        linarith
    · -- Case 3: x < 2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      all_goals
        linarith