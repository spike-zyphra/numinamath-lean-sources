import Mathlib

open Real

theorem algebra_20104 {x : ℝ} (hx : x = 6 + 1 / (2 + 1 / x)) (hx1 : 6 < x):
    ∃ a b c, Squarefree c ∧ c > 0 ∧ x = a + b * sqrt c ∧ a + b + c = 8 := by

  have h1 : x ^ 2 - 6 * x - 3 = 0 := by 
    have h2 : x ≠ 0 := by
      nlinarith 
    have h3 : 2 + 1 / x ≠ 0 := by 
      have h4 : x > 0 := by linarith 
      have h5 : 2 + 1 / x > 0 := by 
        have h6 : 1 / x > 0 := by 
          apply div_pos 
          norm_num 
          linarith 
        nlinarith 
      linarith 
    field_simp [h2] at hx 
    nlinarith

  have h2 : x = 3 + 2 * Real.sqrt 3 := by 
    have h3 : x ^ 2 - 6 * x - 3 = 0 := h1 
    have h4 : x ^ 2 - 6 * x - 3 = (x - (3 + 2 * Real.sqrt 3)) * (x - (3 - 2 * Real.sqrt 3)) := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    rw [h4] at h3 
    cases (mul_eq_zero.mp h3) with 
    | inl h5 => 
      linarith 
    | inr h6 => 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]

  use 3, 2, (3 : ℝ)
  have h4 : (3 : ℝ) > 0 := by 
    norm_num

  constructor
  · -- Show that 3 is squarefree
    have h3s : Squarefree (3 : ℕ) := by 
      native_decide 
    norm_num at h3s ⊢ 
    all_goals norm_num [Real.sqrt_pos] 
  constructor 
  · -- Show that 3 > 0 
    linarith 
  constructor 
  · -- Show that x = 3 + 2 * sqrt 3 
    have eq1 : x = (3 : ℝ) + (2 : ℝ) * Real.sqrt (3 : ℝ) := by 
      linarith [h2, h4]
    rw [eq1]
    all_goals norm_num 
  · -- Show that 3 + 2 + 3 = 8 
    norm_num