import Mathlib

open Real

theorem inequalities_151570 (x : Fin 3 → ℝ) (h₀ : ∀ i, 0 < x i) (h₁ : ∏ i, x i = 1) (h₂ : ∑ i, x i > ∑ i, (1 / x i)) :
    ∃! i, 1 < x i := by
  have h3 : 0 < x 0 := h₀ 0
  have h4 : 0 < x 1 := h₀ 1
  have h5 : 0 < x 2 := h₀ 2
  have h6 : x 0 * x 1 * x 2 = 1 := by
    simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ] at h₁ ⊢
    linarith
  have h7 : ∑ i : Fin 3, (1 / x i) = (1 / x 0) + (1 / x 1) + (1 / x 2) := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  have h8 : ∑ i : Fin 3, x i = x 0 + x 1 + x 2 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  rw [h7, h8] at h₂
  have h9 : 1 / x 0 = x 1 * x 2 := by
    have h9 : x 0 ≠ 0 := by linarith
    field_simp
    nlinarith [h6]
  have h10 : 1 / x 1 = x 0 * x 2 := by
    have h10 : x 1 ≠ 0 := by linarith
    field_simp
    nlinarith [h6]
  have h11 : 1 / x 2 = x 0 * x 1 := by
    have h11 : x 2 ≠ 0 := by linarith
    field_simp
    nlinarith [h6]
  rw [h9, h10, h11] at h₂
  have h14 : (x 0 > 1 ∧ x 1 ≤ 1 ∧ x 2 ≤ 1) ∨ (x 1 > 1 ∧ x 0 ≤ 1 ∧ x 2 ≤ 1) ∨ (x 2 > 1 ∧ x 0 ≤ 1 ∧ x 1 ≤ 1) := by
    by_cases h10 : x 0 > 1
    · -- We have x 0 > 1
      by_cases h11 : x 1 > 1
      · -- We have x 0 > 1 and x 1 > 1
        have h12 : x 2 < 1 := by
          nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, h6, h10, h11]
        nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, mul_pos (sub_pos.mpr h10) (sub_pos.mpr h11), mul_pos (sub_pos.mpr h11) (show 0 < 1 - x 2 by linarith), mul_pos (sub_pos.mpr h10) (show 0 < 1 - x 2 by linarith)]
      · -- We have x 0 > 1 and x 1 ≤ 1
        by_cases h13 : x 2 > 1
        · -- We have x 0 > 1 and x 2 > 1
          have h12 : x 1 < 1 := by
            nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, h6, h10, h13]
          nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, mul_pos (sub_pos.mpr h10) (sub_pos.mpr h13), mul_pos (sub_pos.mpr h13) (show 0 < 1 - x 1 by linarith), mul_pos (sub_pos.mpr h10) (show 0 < 1 - x 1 by linarith)]
        · -- We have x 0 > 1 and x 1 ≤ 1 and x 2 ≤ 1
          left
          constructor
          · exact h10
          constructor
          · -- x 1 ≤ 1
            nlinarith
          · -- x 2 ≤ 1
            nlinarith
    · -- We have x 0 ≤ 1
      by_cases h11 : x 1 > 1
      · -- We have x 1 > 1
        by_cases h14 : x 2 > 1
        · -- We have x 1 > 1 and x 2 > 1
          have h12 : x 0 < 1 := by
            nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, h6, h11, h14]
          nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, mul_pos (sub_pos.mpr h11) (sub_pos.mpr h14), mul_pos (sub_pos.mpr h14) (show 0 < 1 - x 0 by linarith), mul_pos (sub_pos.mpr h11) (show 0 < 1 - x 0 by linarith)]
        · -- We have x 1 > 1 and x 2 ≤ 1
          right
          left
          constructor
          · exact h11
          constructor
          · -- x 0 ≤ 1
            nlinarith
          · -- x 2 ≤ 1
            nlinarith
      · -- We have x 1 ≤ 1
        by_cases h14 : x 2 > 1
        · -- We have x 2 > 1
          right
          right
          constructor
          · exact h14
          constructor
          · -- x 0 ≤ 1
            nlinarith
          · -- x 1 ≤ 1
            nlinarith
        · -- We have x 0 ≤ 1 and x 1 ≤ 1 and x 2 ≤ 1
          exfalso
          nlinarith [mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5, h6]
  rcases h14 with h14 | h14 | h14
  · -- Case where x 0 > 1
    use 0
    constructor
    · exact h14.1
    · intro j
      have h18 : j = 0 ∨ j = 1 ∨ j = 2 := by 
        fin_cases j <;> simp
      rcases h18 with (r | r | r)
      · -- Case j = 0
        rw [r]
        all_goals
          simp [h14.1]
      · -- Case j = 1
        rw [r]
        all_goals
          simp [h14.2.1]
      · -- Case j = 2
        rw [r]
        all_goals
          simp [h14.2.2]
  · -- Case where x 1 > 1
    use 1
    constructor
    · exact h14.1
    · intro j
      have h18 : j = 0 ∨ j = 1 ∨ j = 2 := by 
        fin_cases j <;> simp
      rcases h18 with (r | r | r)
      · -- Case j = 0
        rw [r]
        all_goals
          simp [h14.2.1]
      · -- Case j = 1
        rw [r]
        all_goals
          simp [h14.1]
      · -- Case j = 2
        rw [r]
        all_goals
          simp [h14.2.2]
  · -- Case where x 2 > 1
    use 2
    constructor
    · exact h14.1
    · intro j
      have h18 : j = 0 ∨ j = 1 ∨ j = 2 := by 
        fin_cases j <;> simp
      rcases h18 with (r | r | r)
      · -- Case j = 0
        rw [r]
        all_goals
          simp [h14.2.1]
      · -- Case j = 1
        rw [r]
        all_goals
          simp [h14.2.2]
      · -- Case j = 2
        rw [r]
        all_goals
          simp [h14.1]