import Mathlib

theorem algebra_323848 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : 1 / a ^ 2 + 1 / b ^ 2 = 4 / (a ^ 2 + b ^ 2)) :
    (b / a) ^ 2008 - (a / b) ^ 2009 = 0 ∨ (b / a) ^ 2008 - (a / b) ^ 2009 = 2 := by
  have h1 : a^2 + b^2 ≠ 0 := by
    by_contra h2
    have h3 : a^2 ≥ 0 := sq_nonneg a
    have h4 : b^2 ≥ 0 := sq_nonneg b
    have h5 : a^2 = 0 := by linarith [h2, h3, h4]
    have h6 : a = 0 := pow_eq_zero h5
    contradiction

  field_simp [ha, hb, h1] at h

  have h2 : (a^2 - b^2) ^ 2 = 0 := by
    nlinarith

  have h3 : a^2 - b^2 = 0 := by
    simp [sq_eq_zero_iff] at h2
    linarith

  have h4 : a^2 = b^2 := by linarith

  have h5 : a = b ∨ a = -b := by
    apply eq_or_eq_neg_of_sq_eq_sq
    all_goals nlinarith

  cases h5 with
  | inl h6 =>
    have h7 : b / a = 1 := by
      have h8 : a ≠ 0 := ha
      have h9 : b = a := by linarith [h6]
      rw [h9]
      field_simp [h8]
    have h10 : a / b = 1 := by
      have h11 : b ≠ 0 := hb
      have h12 : a = b := by linarith [h6]
      rw [h12]
      field_simp [h11]
    have h13 : (b / a) ^ 2008 - (a / b) ^ 2009 = 0 := by
      rw [h7, h10]
      norm_num
    left
    linarith
  | inr h6 =>
    have h7 : b / a = -1 := by
      have h8 : a ≠ 0 := ha
      have h9 : a = -b := by linarith [h6]
      rw [h9]
      field_simp [hb]
      <;> nlinarith
    have h10 : a / b = -1 := by
      have h11 : b ≠ 0 := hb
      have h12 : a = -b := by linarith [h6]
      rw [h12]
      field_simp [hb]
      <;> nlinarith
    have h13 : (b / a) ^ 2008 - (a / b) ^ 2009 = 2 := by
      rw [h7, h10]
      norm_num
    right
    linarith