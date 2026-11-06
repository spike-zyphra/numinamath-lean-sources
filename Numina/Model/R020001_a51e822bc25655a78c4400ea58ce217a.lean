import Mathlib

open Real Set
open scoped Real

theorem algebra_95275 {A B : ℝ} (hA : A = 20 * π / 180) (hB : B = 25 * π / 180) :
    (1 + tan A) * (1 + tan B) = 2 := by
  rw [hA, hB]
  have h3 : 20 * π / 180 + 25 * π / 180 = Real.pi / 4 := by 
    linarith [Real.pi_pos]
  have h6 : tan (Real.pi / 4 : ℝ) = 1 := by 
    exact tan_pi_div_four
  have h7 : tan (20 * π / 180 + 25 * π / 180) = 1 := by
    rw [show 20 * π / 180 + 25 * π / 180 = Real.pi / 4 by linarith [Real.pi_pos]]
    exact h6
  have h8 : tan (20 * π / 180 : ℝ) + tan (25 * π / 180 : ℝ) = 1 - tan (20 * π / 180 : ℝ) * tan (25 * π / 180 : ℝ) := by
    have h9 : ∀ (k : ℤ), (20 * π / 180 : ℝ) ≠ (2 * ↑k + 1) * Real.pi / 2 := by 
      intro k 
      by_contra h 
      have h10 : (20 * π / 180 : ℝ) = (2 * ↑k + 1) * Real.pi / 2 := by 
        linarith 
      have h11 : Real.pi > 0 := Real.pi_pos 
      have h12 : (20 * π / 180 : ℝ) > 0 := by 
        nlinarith [Real.pi_pos] 
      have h13 : (2 * (↑k : ℝ) + 1) * Real.pi / 2 > 0 := by 
        nlinarith [Real.pi_pos] 
      have h14 : (20 * π / 180 : ℝ) = (2 * (↑k : ℝ) + 1) * Real.pi / 2 := by 
        linarith [h10] 
      have h15 : (↑k : ℝ) > -10 := by 
        nlinarith [Real.pi_pos, h14] 
      have h16 : k > -10 := by 
        by_contra h 
        push_neg at h 
        have h17 : (↑k : ℝ) ≤ (-10 : ℝ) := by 
          exact_mod_cast h 
        nlinarith [Real.pi_pos] 
      have h17 : k < 10 := by 
        by_contra h 
        push_neg at h 
        have h18 : (↑k : ℝ) ≥ (10 : ℝ) := by 
          exact_mod_cast h 
        nlinarith [Real.pi_pos] 
      interval_cases k <;> norm_num at h10 <;> 
        linarith [Real.pi_pos, Real.pi_lt_315] 
    have h10 : ∀ (l : ℤ), (25 * π / 180 : ℝ) ≠ (2 * ↑l + 1) * Real.pi / 2 := by 
      intro l 
      by_contra h 
      have h11 : (25 * π / 180 : ℝ) = (2 * ↑l + 1) * Real.pi / 2 := by 
        linarith 
      have h12 : Real.pi > 0 := Real.pi_pos 
      have h13 : (25 * π / 180 : ℝ) > 0 := by 
        nlinarith [Real.pi_pos] 
      have h14 : (2 * (↑l : ℝ) + 1) * Real.pi / 2 > 0 := by 
        nlinarith [Real.pi_pos] 
      have h15 : (25 * π / 180 : ℝ) = (2 * (↑l : ℝ) + 1) * Real.pi / 2 := by 
        linarith [h11] 
      have h16 : (↑l : ℝ) > -10 := by 
        nlinarith [Real.pi_pos, h15] 
      have h17 : l > -10 := by 
        by_contra h 
        push_neg at h 
        have h18 : (↑l : ℝ) ≤ (-10 : ℝ) := by 
          exact_mod_cast h 
        nlinarith [Real.pi_pos] 
      have h18 : l < 10 := by 
        by_contra h 
        push_neg at h 
        have h19 : (↑l : ℝ) ≥ (10 : ℝ) := by 
          exact_mod_cast h 
        nlinarith [Real.pi_pos] 
      interval_cases l <;> norm_num at h11 <;> 
        linarith [Real.pi_pos, Real.pi_lt_315] 
    have h11 : tan (20 * π / 180 + 25 * π / 180 : ℝ) = (tan (20 * π / 180 : ℝ) + tan (25 * π / 180 : ℝ)) / (1 - tan (20 * π / 180 : ℝ) * tan (25 * π / 180 : ℝ)) := by 
      rw [tan_add]
      all_goals 
        simp [h9, h10]
        <;> nlinarith [Real.pi_pos, Real.pi_lt_315] 
    rw [h7] at h11 
    have h12 : (tan (20 * π / 180 : ℝ) + tan (25 * π / 180 : ℝ)) / (1 - tan (20 * π / 180 : ℝ) * tan (25 * π / 180 : ℝ)) = 1 := by 
      linarith 
    have h13 : (tan (20 * π / 180 : ℝ) + tan (25 * π / 180 : ℝ)) / (1 - tan (20 * π / 180 : ℝ) * tan (25 * π / 180 : ℝ)) = 1 := h12 
    have h14 : 1 - tan (20 * π / 180 : ℝ) * tan (25 * π / 180 : ℝ) ≠ 0 := by 
      by_contra h 
      have h15 : (tan (20 * π / 180 : ℝ) + tan (25 * π / 180 : ℝ)) / (1 - tan (20 * π / 180 : ℝ) * tan (25 * π / 180 : ℝ)) = 0 := by 
        rw [h] 
        norm_num 
      linarith [h15, h13] 
    field_simp at h13 ⊢ 
    all_goals 
      nlinarith 
  have h9 : (1 + tan (20 * π / 180 : ℝ)) * (1 + tan (25 * π / 180 : ℝ)) = 2 := by
    nlinarith [h8] 
  exact h9