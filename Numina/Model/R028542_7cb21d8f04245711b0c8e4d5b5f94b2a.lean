import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_186850 (x : ℝ) :
  (1 - 0.4 * x^2) / (5 - x) ≥ 2 * x / 5 ↔
  x ≤ 1 / 2 ∨ x > 5 := by
  constructor
  · -- Assume $\frac{1-0.4 x^{2}}{5-x} \geq \frac{2x}{5}$, prove $x \leq \frac{1}{2} \lor x > 5$.
    intro h
    have h1 : (1 - 0.4 * x^2) / (5 - x) - 2 * x / 5 ≥ 0 := by
      linarith

    by_cases h2 : 5 - x = 0
    · -- If 5 - x = 0, then x = 5, which makes the original hypothesis false
      have eq1 : x = 5 := by linarith
      rw [eq1] at h
      norm_num at h

    · -- Case 5 - x ≠ 0
      have h3 : (1 - 0.4 * x^2) / (5 - x) - 2 * x / 5 =
          (5 - 10 * x) / (5 * (5 - x)) := by
        have h4 : 5 - x ≠ 0 := by
          intro h5
          apply h2
          linarith
        field_simp [h4]
        ring
      rw [h3] at h1
      have h4 : (5 - 10 * x) / (5 * (5 - x)) ≥ 0 := h1
      by_cases h5 : 5 * (5 - x) > 0
      · -- If 5 * (5 - x) > 0, then 5 - 10x ≥ 0
        have h6 : 5 - 10 * x ≥ 0 := by 
          apply (div_nonneg_iff).mp at h4
          cases h4 with
          | inl h =>
            linarith
          | inr h =>
            nlinarith
        have h8 : x ≤ 1 / 2 := by
          linarith
        left
        tauto

      · -- Case 5 * (5 - x) ≤ 0
        by_cases h6 : 5 * (5 - x) < 0
        · -- If 5 * (5 - x) < 0, then 5 - 10x ≤ 0
          have h7 : 5 - 10 * x ≤ 0 := by 
            apply (div_nonneg_iff).mp at h4
            cases h4 with 
            | inl h => 
              linarith 
            | inr h => 
              linarith 
          have h8 : x > 5 := by 
            nlinarith 
          right 
          linarith 

        · -- Case 5 * (5 - x) = 0
          have h7 : 5 * (5 - x) = 0 := by 
            nlinarith 
          have h8 : 5 - x = 0 := by 
            nlinarith 
          contradiction

  · -- Assume $x \leq \frac{1}{2} \lor x > 5$, prove $\frac{1-0.4 x^{2}}{5-x} \geq \frac{2x}{5}$.
    rintro (h | h)
    · -- If x ≤ 1/2 
      by_cases h2 : 5 - x = 0
      · -- If 5 - x = 0 
        have eq1 : x = 5 := by linarith 
        nlinarith 
      · -- Case 5 - x ≠ 0 
        have h4 : 5 - x ≠ 0 := by 
          intro h5 
          apply h2 
          all_goals linarith 
        have h5 : (1 - 0.4 * x^2) / (5 - x) - 2 * x / 5 ≥ 0 := by 
          have h51 : (1 - 0.4 * x^2) / (5 - x) - 2 * x / 5 = (5 - 10 * x) / (5 * (5 - x)) := by 
            field_simp [h4] 
            ring 
          rw [h51] 
          have h6 : 5 * (5 - x) > 0 := by 
            nlinarith 
          have h7 : 5 - 10 * x ≥ 0 := by 
            nlinarith 
          apply div_nonneg 
          all_goals 
          all_goals linarith 
        linarith

    · -- If x > 5 
      by_cases h2 : 5 - x = 0 
      · -- Case x = 5 
        nlinarith 
      · -- Case 5 - x ≠ 0 
        have h4 : 5 - x ≠ 0 := by 
          intro h5 
          apply h2 
          linarith 
        have h5 : (1 - 0.4 * x^2) / (5 - x) - 2 * x / 5 ≥ 0 := by 
          have h51 : (1 - 0.4 * x^2) / (5 - x) - 2 * x / 5 = (5 - 10 * x) / (5 * (5 - x)) := by 
            field_simp [h4] 
            ring 
          rw [h51] 
          have h7 : 5 * (5 - x) < 0 := by 
            nlinarith 
          have h8 : 5 - 10 * x ≤ 0 := by 
            nlinarith 
          have h9 : (5 - 10 * x) / (5 * (5 - x)) ≥ 0 := by 
            apply div_nonneg_of_nonpos 
            all_goals 
            all_goals linarith 
          linarith 
        linarith