import Mathlib

theorem algebra_318553 {a b : ℝ} (hab : a * b = 1) :
    1 / (1 + a) + 1 / (1 + b) = a / (1 + a) + b / (1 + b) := by
  have h1 : a = -1 ↔ b = -1 := by
    constructor
    · -- Assume a = -1, prove b = -1
      intro ha
      have ha_ne_zero : a ≠ 0 := by
        by_contra h
        rw [h] at ha
        norm_num at ha
      rw [ha] at hab
      have hb_ne_zero : b ≠ 0 := by
        by_contra h
        rw [h] at hab
        norm_num at hab
      have : -1 * b = 1 := hab
      have b_eq_neg_one : b = -1 := by
        have eq1 : -1 * b = 1 := this
        have eq2 : b = -1 := by
          field_simp [hb_ne_zero] at eq1 ⊢
          all_goals
            linarith
        assumption
      assumption
    · -- Assume b = -1, prove a = -1
      intro hb
      have hb_ne_zero : b ≠ 0 := by
        by_contra h
        rw [h] at hb
        norm_num at hb
      rw [hb] at hab
      have ha_ne_zero : a ≠ 0 := by
        by_contra h
        rw [h] at hab
        norm_num at hab
      have : a * -1 = 1 := hab
      have a_eq_neg_one : a = -1 := by
        have eq1 : a * -1 = 1 := this
        have eq2 : a = -1 := by
          field_simp [ha_ne_zero] at eq1 ⊢
          all_goals
            linarith
        assumption
      assumption
  by_cases h2 : a = -1
  · -- If a = -1, then b = -1 as shown in h1
    have h3 : b = -1 := h1.mp h2
    rw [h2, h3]
    norm_num
    all_goals norm_num
  · -- Case where a ≠ -1
    have ha_ne_zero : a ≠ 0 := by
      by_contra h
      rw [h] at hab
      norm_num at hab
    have hb_ne_zero : b ≠ 0 := by
      by_contra h
      rw [h] at hab
      norm_num at hab
    have h4 : 1 + a ≠ 0 := by
      intro h
      apply h2
      linarith
    have h5 : 1 + b ≠ 0 := by
      by_contra h
      have h6 : b = -1 := by linarith
      have h7 : a = -1 := by
        rw [show b = -1 by linarith] at hab
        have : a * -1 = 1 := by linarith [hab]
        have ha_ne_zero : a ≠ 0 := by
          by_contra h
          rw [h] at this
          norm_num at this
        have h8 : a = -1 := by
          have eq1 : a * -1 = 1 := this
          have eq2 : a = -1 := by
            field_simp [ha_ne_zero] at eq1 ⊢
            all_goals
              linarith
          assumption
        assumption
      contradiction
    field_simp [(show 1 + a ≠ 0 by assumption), (show 1 + b ≠ 0 by assumption)]
    <;> nlinarith [hab, sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b + 1)]