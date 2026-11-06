import Mathlib
/-If $\left| 1-\sqrt{{{(x-1)}^{2}}} \right|=x$, then the range of real number $x$ is ___          ___ .-/
theorem algebra_1144 (x : ℝ)  :
    |1 - Real.sqrt ((x - 1)^2)| = x ↔ 0 ≤ x ∧ x ≤ 1 := by
  have h1 : Real.sqrt ((x - 1) ^ 2) = |x - 1| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1]
  constructor
  · -- Forward direction: |1 - |x - 1|| = x → x ≤ 1
    intro h
    by_cases h2 : 1 - |x - 1| ≥ 0
    · -- Case 1: 1 - |x - 1| ≥ 0, so |1 - |x - 1|| = 1 - |x - 1|
      have h5 : 0 ≤ x := by
        rw[←h]
        norm_num
      rw [abs_of_nonneg h2] at h
      have h3 : |x - 1| = 1 - x := by linarith
      have h4 : x ≤ 1 := by
        have h5 : |x - 1| ≥ 0 := abs_nonneg (x - 1)
        linarith
      constructor
      · exact h5
      · exact h4
    · -- Case 2: 1 - |x - 1| < 0, so |1 - |x - 1|| = |x - 1| - 1
      push_neg at h2
      rw [abs_of_neg h2] at h
      have h3 : |x - 1| = x + 1 := by linarith
      by_cases h4 : x - 1 ≥ 0
      · -- Case 2a: x - 1 ≥ 0, so |x - 1| = x - 1
        rw [abs_of_nonneg h4] at h3
        linarith
      · -- Case 2b: x - 1 < 0, so |x - 1| = -(x - 1) = 1 - x
        push_neg at h4
        rw [abs_of_neg h4] at h3
        nlinarith [abs_nonneg (x - 1)]
  · -- Backward direction: x ≤ 1 → |1 - |x - 1|| = x
    intro h
    have h1 : x - 1 ≤ 0 := by linarith
    have h2 : |x - 1| = 1 - x := by
      rw [abs_of_nonpos h1]
      ring
    have h3 : |(1 - |x - 1|)| = x := by
      rw [h2]
      rw [abs_of_nonneg (by linarith)]
      all_goals linarith
    simp [h3]
