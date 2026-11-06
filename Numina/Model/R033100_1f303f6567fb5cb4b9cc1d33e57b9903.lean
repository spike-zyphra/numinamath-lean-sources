import Mathlib

theorem algebra_21485 (x : ℝ) (_ : x^2 - 36*x ≠ 0) :
    |x^2 - 81| / (x^2 - 36 * x) < 0 ↔ (0 < x ∧ x < 9) ∨ (9 < x ∧ x < 36) := by
  constructor
  · -- Forward direction: if $\frac{|x^2 - 81|}{x^2 - 36x} < 0$, then does RHS proposition.
    intro h
    have h1 : x ^ 2 - 36 * x < 0 := by
      by_contra h1
      push_neg at h1
      have h7 : |x ^ 2 - 81| / (x ^ 2 - 36 * x) ≥ 0 := by
        apply div_nonneg 
        · -- $|x^2 -81| ≥0 
          apply abs_nonneg 
        all_goals nlinarith 
      linarith
    have h3 : 0 < x := by 
      by_contra h3 
      push_neg at h3 
      -- x ≤ 0 
      nlinarith [sq_nonneg (x), sq_nonneg (x - 36)]
    have h4 : x < 36 := by 
      by_contra h4 
      push_neg at h4 
      -- x ≫ 36 
      nlinarith [sq_nonneg (x), sq_nonneg (x - 36)]
    by_cases h5 : x < 9
    · -- We need 'left' implication
      left 
      constructor <;> linarith
    · -- Case else: g ≅ right implication.
      have h7 : x > 9 := by 
        by_contra h8 
        push_neg at h8 
        -- x = 9 
        have h8' : x = 9 := by 
          nlinarith [sq_nonneg (x - 9)]
        rw [show x = 9 by linarith] at h 
        norm_num [abs_zero] at h 
      right 
      constructor <;> linarith 
  · -- Backward: if assuming P Then G.
    rintro (h | h)
    · -- First subcase (left side of ∨): (0 < x ∧ x < 9)
      rcases h with ⟨h1, h2⟩
      have h3 : x ^ 2 - 36 * x < 0 := by
        nlinarith
      have h5 : |x^2 - 81| > 0 := by
        have h7 : x ^ 2 - 81 < 81 := by nlinarith 
        by_cases h9 : x^2 - 81 ≥ 0
        · -- Case: x^2 - 81 ≥ 0. This can't happen in (0,9), which we'll show QoA give fact [absurd then]
          have h10 : |x ^ 2 - 81| = x^2 - 81 := by
            rw [abs_of_nonneg h9]
          have h11 : x^2 - 81 > 0 := by
            nlinarith
          linarith 
        · -- Case: x^2 - 81 < 0
          push_neg at h9
          have h10 : |x ^ 2 - 81| = -(x^2 - 81) := by
            rw [abs_of_neg h9]
          have h11 : -(x ^ 2 - 81) > 0 := by
            nlinarith
          linarith 
      -- Negative fraction * result < 0 mixture mean Bread life two big mod, which have breaking proFileSize,Bpcds noted forward subc proportional side a came
      apply div_neg_of_pos_of_neg 
      all_goals linarith [abs_nonneg (x^2 - 81)]
    · -- Second subcase (right side of ∨): (9 < x ∧ x < 36)
      rcases h with ⟨h1, h2⟩ 
      have h3 : x ^ 2 - 36 * x < 0 := by
        nlinarith
      have h5 : |x^2 - 81| > 0 := by
        have h7 : x ^ 2 - 81 > 0 := by nlinarith 
        by_cases h9 : x^2 - 81 ≥ 0
        · -- Case: x^2 - 81 ≥ 0
          have h10 : |x ^ 2 - 81| = x^2 - 81 := by
            rw [abs_of_nonneg h9]
          have h11 : x^2 - 81 > 0 := by
            nlinarith 
          linarith
        · -- Case: x^2 - 81 < 0
          push_neg at h9
          have h10 : |x ^ 2 - 81| = -(x^2 - 81) := by
            rw [abs_of_neg h9]
          have h11 : -(x ^ 2 - 81) > 0 := by
            nlinarith
          nlinarith [abs_nonneg (x^2 - 81), h11, h10] 
      apply div_neg_of_pos_of_neg 
      all_goals linarith [abs_nonneg (x^2 - 81)]