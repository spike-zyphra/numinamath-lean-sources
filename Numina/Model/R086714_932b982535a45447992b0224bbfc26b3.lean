import Mathlib

theorem algebra_2843 (x : ℝ) :
    (|x - 3| - 2 ≥ 0 ∧ x^2 - 4 * x + 3 ≠ 0) ↔
    (x < 1 ∨ x ≥ 5) := by
  constructor
  · -- (→) direction: if the original conditions hold then x < 1 ∨ x ≥ 5
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : |x - 3| ≥ 2 := by linarith
    cases' abs_cases (x - 3) with h4 h4
    · -- Case where x - 3 ≥ 0, so |x - 3| = x - 3
      have h5 : x - 3 ≥ 2 := by linarith
      have h6 : x ≥ 5 := by linarith
      right
      linarith
    · -- Case where x - 3 < 0, so |x - 3| = -(x - 3)
      have h2 : x - 3 ≤ -2 := by linarith
      have h12 : x ≤ 1 := by linarith
      have h9 : x < 1 := by
        by_contra h10
        push_neg at h10
        have h11 : x ≥ 1 := by linarith
        have h11' : x = 1 := by linarith [h12, h11]
        have h0 : x^2 - 4 * x + 3 = 0 := by
          rw [show x = 1 by linarith [h11']]
          norm_num
        contradiction
      left
      linarith
  · -- (←) direction: if x < 1 ∨ x ≥ 5, then the original conditions
    rintro (h | h)
    · -- Assume x < 1
      constructor
      · -- Show |x - 3| - 2 ≥ 0
        have h1 : x - 3 < -2 := by linarith
        have h3 : |x - 3| ≥ 2 := by
          rw [abs_of_neg (show x - 3 < 0 by linarith)]
          linarith
        linarith
      · -- Show x^2 - 4 * x + 3 ≠ 0
        by_contra h0
        have h2 : x < 1 := by linarith
        have h01 : (x - 1) * (x - 3) = 0 := by nlinarith
        cases' (mul_eq_zero.mp h01) with h02 h03
        · -- h02: x - 1 = 0 → x = 1, contradiction
          have : x = 1 := by linarith
          linarith
        · -- h03: x - 3 = 0 → x = 3, contradiction
          have : x = 3 := by linarith
          linarith
    · -- Assume x ≥ 5
      constructor
      · -- Show |x - 3| - 2 ≥ 0
        have h2 : x - 3 ≥ 2 := by linarith
        have h3 : |x - 3| ≥ 2 := by
          rw [abs_of_nonneg (show x - 3 ≥ 0 by linarith)]
          linarith
        linarith
      · -- Show x^2 - 4 * x + 3 ≠ 0
        by_contra h0
        have h1 : x ≥ 5 := by linarith
        have h01 : (x - 1) * (x - 3) = 0 := by nlinarith
        cases' (mul_eq_zero.mp h01) with h02 h03
        · -- h02: x - 1 = 0 → x = 1, contradiction
          have : x = 1 := by linarith
          linarith
        · -- h03: x - 3 = 0 → x = 3, contradiction
          have : x = 3 := by linarith
          linarith