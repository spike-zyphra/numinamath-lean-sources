import Mathlib

theorem algebra_1611 (x : ℝ) (hx : x ≠ 1 ∧ x ≠ -1) (h : x / (|x| - 1) = 1) :
    (|x| + 1) / (2 * x) = -3 / 2 := by
  have hx1 : x ≠ 1 := hx.1
  have hx2 : x ≠ -1 := hx.2

  have h1 : |x| - 1 ≠ 0 := by 
    by_contra h1
    have h2 : |x| = 1 := by linarith [h1]
    cases eq_or_eq_neg_of_abs_eq h2 with
    | inl h3 =>
      exfalso
      apply hx1
      linarith [h3]
    | inr h4 =>
      exfalso
      apply hx2
      linarith [h4]

  have eq1 : x = |x| - 1 := by
    have h1' : |x| - 1 ≠ 0 := h1 
    field_simp [h1'] at h 
    linarith

  by_cases h2 : x ≥ 0 
  · -- x ≥ 0, so |x| = x
    have h3 : |x| = x := abs_of_nonneg h2 
    rw [h3] at eq1 
    linarith 
  · -- x < 0, so |x| = -x
    have h4 : x < 0 := by linarith 
    have h5 : |x| = -x := abs_of_neg h4 
    rw [h5] at eq1 
    have h6 : x = -1 / 2 := by 
      linarith 
    have h7 : |x| = 1 / 2 := by 
      rw [abs_of_neg (show x < 0 by linarith)]
      linarith [h6]
    have h8 : 2 * x ≠ 0 := by 
      intro h0 
      have h9 : x = 0 := by linarith 
      linarith [h6, h9]
    have eq2 : (|x| + 1) / (2 * x) = -3 / 2 := by 
      rw [show |x| = 1 / 2 by linarith [h7], show x = -1 / 2 by linarith [h6]]
      norm_num 
    exact_mod_cast eq2