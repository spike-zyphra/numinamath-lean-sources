import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_252397 (x : ℝ) :
  (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = 4 ↔ x = 4 ∨ x = 2 := by
  constructor
  · -- Assume (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = 4, prove x = 4 ∨ x = 2
    intro h
    have h1 : abs (x - 3) > 0 := by
      by_contra h3
      push_neg at h3
      have h4 : abs (x - 3) = 0 := by linarith [abs_nonneg (x - 3)]
      have h5 : x - 3 = 0 := abs_eq_zero.mp h4
      have h6 : x = 3 := by linarith
      rw [h6] at h
      norm_num [abs_zero] at h
      all_goals try { linarith }
      all_goals try { tauto }
    have eq₁ : abs (x - 3) + 1 / abs (x - 3) = (2 : ℝ) := by
      have h2 : (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = 4 := h
      have h3 : -abs (x - 3) - 1 / abs (x - 3) = - (2 : ℝ) := by
        have h4 : (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = 4 := h2
        have h5 : (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = 4 := h4
        have h8 : (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = (1 / 2 : ℝ) ^ (- (2 : ℝ)) := by
          rw [h5]
          norm_num
        have h9 : -abs (x - 3) - 1 / abs (x - 3) = - (2 : ℝ) := by
          apply_fun (Real.logb (1 / 2 : ℝ)) at h8
          simp at h8 ⊢
          all_goals try { linarith }
          all_goals try { tauto }
          all_goals norm_num
          all_goals try tauto
        linarith
        all_goals try { nlinarith }
        all_goals try tauto
        all_goals norm_num
        all_goals try tauto
        all_goals norm_num
        all_goals try tauto
        all_goals try { tauto }
        all_goals norm_num
        all_goals try { tauto }
        all_goals norm_num
        all_goals try { tauto }
      have h4 : abs (x - 3) + 1 / abs (x - 3) = (2 : ℝ) := by
        have h5 : abs (x - 3) > 0 := h1
        have h6 : abs (x - 3) + 1 / abs (x - 3) = (2 : ℝ) := by
          have h7 : -abs (x - 3) - 1 / abs (x - 3) = - (2 : ℝ) := by
            linarith [h3]
          have h8 : abs (x - 3) + 1 / abs (x - 3) = (2 : ℝ) := by
            linarith [h7]
          linarith
        linarith
      linarith
      all_goals try tauto
      all_goals try { norm_num }
      all_goals try tauto
      all_goals try { tauto }
      all_goals try { nlinarith }
      all_goals try { tauto }
      all_goals try { tauto }
      all_goals try { tauto }
      all_goals try { tauto }
      all_goals try { tauto }
      all_goals try { tauto }
    have eq₂ : abs (x - 3) = (1 : ℝ) := by
      have h4 : abs (x - 3) > 0 := h1
      have h7 : abs (x - 3) + 1 / abs (x - 3) = (2 : ℝ) := eq₁
      have h8 : abs (x - 3) = (1 : ℝ) := by
        have h9 : abs (x - 3) > 0 := h4
        have eq3 : abs (x - 3) ^ 2 + 1 = 2 * abs (x - 3) := by
          have h10 : abs (x - 3) > 0 := h9
          have eq4 : abs (x - 3) + 1 / abs (x - 3) = (2 : ℝ) := by
            linarith [h7]
          have h11 : abs (x - 3) ^ 2 + 1 = 2 * abs (x - 3) := by
            have h12 : abs (x - 3) > 0 := h10
            field_simp at eq4 ⊢
            nlinarith [sq_nonneg (abs (x - 3) : ℝ)]
          linarith [h11]
        have h12 : (abs (x - 3) - 1) ^ 2 = (0 : ℝ) := by
          nlinarith [sq_nonneg (abs (x - 3) - 1 : ℝ)]
        have h13 : abs (x - 3) - 1 = (0 : ℝ) := by
          rw [sq_eq_zero_iff] at h12
          linarith [h12]
        linarith
      linarith
    cases' eq_or_eq_neg_of_abs_eq eq₂ with h8 h9
    · -- Case where x - 3 = 1
      left
      linarith
    · -- Case where x - 3 = -1
      right
      linarith
  · -- Assume x = 4 ∨ x = 2, prove (1 / 2 : ℝ) ^ (-abs (x - 3) - 1 / abs (x - 3)) = 4
    rintro (h | h)
    · -- Case x = 4
      rw [h]
      norm_num [abs_of_pos]
      <;> norm_num
    · -- Case x = 2
      rw [h]
      norm_num [abs_of_neg]
      <;> norm_num