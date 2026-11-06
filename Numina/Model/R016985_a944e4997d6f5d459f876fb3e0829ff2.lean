import Mathlib

theorem inequalities_207559 (x : ℝ) (hx : x ≠ 1) :
    x^3 - 3 * x^2 + x + 1 + 1 / (x - 1) ≥ 0 ↔ x = 0 ∨ x > 1 := by
  constructor
  · -- Assume the inequality holds, prove x = 0 ∨ x > 1
    intro h
    have h1 : x - 1 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h2 : x^3 - 3 * x^2 + x + 1 + 1 / (x - 1) = (x^2 * (x - 2) ^ 2 ) / (x - 1) := by
      field_simp [(show x - 1 ≠ 0 by exact h1)]
      ring
    rw [h2] at h
    by_cases h4 : x - 1 > 0
    · -- x - 1 > 0, so x > 1
      have h4' : x > 1 := by linarith
      right
      linarith
    · -- x - 1 ≤ 0
      have h4 : x - 1 < 0 := by
        by_contra h
        push_neg at h
        have : x = 1 := by linarith [show x - 1 = 0 by linarith]
        tauto
      -- $\frac{x^2*(x - 2)^2}{x - 1} \geq0$ with x -1 <0 means numerator ≤0
      have h5 : x^2 * (x - 2) ^ 2 ≤ (0 : ℝ) := by
        have h6 : (x^2 * (x - 2) ^ 2 ) / (x - 1) ≥ 0 := by linarith [h]
        apply (le_div_iff_of_neg' (by linarith)).mp at h6
        nlinarith
      have h3 : x^2 * (x - 2) ^ 2 ≥ 0 := by
        positivity
      -- x^2*(x - 2)^2 = 0
      have h6 : x^2 * (x - 2) ^ 2 = 0 := by
        linarith
      have : x = 0 := by
        cases' (mul_eq_zero.1 h6) with h7 h8
        · -- x ^ 2 = 0
          have h10 : x ^ 2 = 0 := by linarith
          have h11 : x = 0 := by
            nlinarith
          exact h11
        · -- (x - 2) ^ 2 = 0
          have h12 : (x - 2) ^ 2 = 0 := by linarith
          have h13 : x - 2 = 0 := by
            nlinarith
          have h14 : x = 2 := by
            linarith
          nlinarith [show x < (1 : ℝ) by linarith]
      left
      linarith
  · -- Assume x = 0 ∨ x > 1, prove the inequality
    rintro (h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x > 1
      have h1 : x - 1 > 0 := by
        linarith
      have h2 : x^3 - 3 * x^2 + x + 1 + 1 / (x - 1) = (x^2 * (x - 2) ^ 2 ) / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by
          intro h
          apply hx
          linarith
        )]
        ring
      rw [h2]
      apply div_nonneg
      · -- Show that x^2 * (x - 2) ^ 2 ≥ 0
        positivity
      · -- Show that x - 1 ≥ 0
        linarith