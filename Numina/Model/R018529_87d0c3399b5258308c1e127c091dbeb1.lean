import Mathlib

theorem algebra_118066 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hge : ∃ r, b = a * r ∧ c = b * r) :
    ∃ x1 x2, x1 ≠ x2 ∧ a * x1 ^ 2 + 2 * Real.sqrt 2 * b * x1 + c = 0 ∧
    a * x2 ^ 2 + 2 * Real.sqrt 2 * b * x2 + c = 0 := by

  rcases hge with ⟨r, hbr, hcr⟩
  have h1 : c = a * r ^ 2 := by 
    rw [hcr, hbr]
    all_goals ring
  have h2 : b ^ 2 = a * c := by
    rw [h1, hbr]
    all_goals ring
  have h3 : (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c = 4 * b ^ 2 := by
    have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      (2 * Real.sqrt 2 * b) ^ 2 - 4 * a * c = 4 * ((Real.sqrt 2) ^ 2) * (b ^ 2) - 4 * a * c := by
        ring
      _ = 4 * (2) * (b ^ 2) - 4 * a * c := by 
        rw [h4]
      _ = 8 * (b ^ 2) - 4 * a * c := by 
        ring
      _ = 8 * (b ^ 2) - 4 * (a * c) := by 
        ring
      _ = 4 * b ^ 2 := by 
        have h4 : a * c = b ^ 2 := by 
          linarith [h2]
        rw [h4]
        all_goals nlinarith
  
  use (- Real.sqrt 2 * b + b) / a, (- Real.sqrt 2 * b - b) / a
  
  constructor
  · -- Show that x1 ≠ x2
    by_contra h
    have h4 : (- Real.sqrt 2 * b + b) / a = (- Real.sqrt 2 * b - b) / a := by 
      linarith [h]
    have h5 : - Real.sqrt 2 * b + b = - Real.sqrt 2 * b - b := by
      field_simp [ha] at h4 ⊢
      all_goals linarith
    have h6 : b = 0 := by 
      nlinarith
    contradiction
  constructor
  · -- Show that the first root satisfies the equation
    field_simp [ha]
    nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, h2 ]
  · -- Show that the second root satisfies the equation
    field_simp [ha]
    nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, h2 ]