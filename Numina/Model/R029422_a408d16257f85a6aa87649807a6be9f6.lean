import Mathlib

theorem algebra_12032 : {x : ℝ | x ≠ -5 ∧ (x ^ 2 - 25) / (x + 5) < 0} = Set.Iio (-5) ∪ Set.Ioo (-5) 5 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo]
  constructor
  · -- Assume x ≠ -5 and (x ^ 2 - 25) / (x + 5) < 0
    intro h
    rcases h with ⟨h1, h2⟩
    have h4 : x + 5 ≠ 0 := by
      intro h5
      apply h1
      linarith
    have h5 : (x ^ 2 - 25) / (x + 5) = x - 5 := by
      have h7 : x + 5 ≠ 0 := h4
      field_simp [(show x + 5 ≠ 0 by assumption)]
      <;> ring
    rw [h5] at h2
    have h6 : x < 5 := by linarith
    by_cases h7 : x < -5
    · -- x < -5
      left
      exact_mod_cast h7
    · -- -5 ≤ x < 5
      have h7 : -5 ≤ x := by linarith
      have h10 : -5 < x := by
        by_contra h9
        push_neg at h9
        have h10 : x = -5 := by linarith
        exfalso
        apply h1
        linarith
      right
      constructor <;> linarith
  · -- Show {x : ℝ | x ≠ -5 ∧ (x ^ 2 - 25) / (x + 5) < 0} ⊇ (Set.Iio (-5) ∪ Set.Ioo (-5) 5)
    rintro (h | ⟨h1, h2⟩)
    · -- Case x < -5
      constructor
      · -- Show x ≠ -5
        linarith
      · -- Show $\frac{x ^ 2 - 25}{x + 5} < 0$
        have h13 : x ^ 2 - 25 > 0 := by nlinarith
        have h14 : x + 5 < 0 := by nlinarith
        apply div_neg_of_pos_of_neg
        all_goals
        try linarith
    · -- Case -5 < x < 5
      constructor
      · -- Show x ≠ -5
        nlinarith
      · -- Show $\frac{x ^ 2 - 25}{x + 5} < 0$
        have h13 : x ^ 2 - 25 < 0 := by nlinarith
        have h14 : x + 5 > 0 := by nlinarith
        apply div_neg_of_neg_of_pos
        all_goals
        try linarith