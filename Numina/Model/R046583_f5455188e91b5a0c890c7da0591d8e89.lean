import Mathlib

theorem algebra_235950 (x : ℝ) (h : max (max 1 2) (max 3 x) = 1 + 2 + 3 + x) :
    x = -3 := by
  have h1 : max (max 1 2) (max 3 x) = max 3 x := by
    have h5 : max 1 2 = (2 : ℝ) := by norm_num
    have h6 : max (max 1 2) (max 3 x) = max 2 (max 3 x) := by
      simp [h5]
    have h3 : max 3 x ≥ (3 : ℝ) := by
      cases max_cases 3 x with
      | inl h4 =>
        linarith
      | inr h5 => 
        linarith
    have h10 : max 2 (max 3 x) = max 3 x := by
      have h11 : max 3 x ≥ (2 : ℝ) := by 
        have h12 : max 3 x ≥ (3 : ℝ) := h3
        linarith
      rw [max_eq_right]
      linarith
    linarith [h6, h10]
  have heq : max 3 x = 6 + x := by
    have heq : max (max 1 2) (max 3 x) = 6 + x := by
      linarith [h]
    rw [h1] at heq
    linarith
  by_cases h2 : x ≤ 3
  · -- Case x ≤ 3, then max 3 x = 3
    have h3 : max 3 x = 3 := by
      apply max_eq_left
      linarith
    rw [h3] at heq
    linarith
  · -- Case where x > 3.
    have h4 : max 3 x = x := by
      apply max_eq_right
      linarith
    rw [h4] at heq
    linarith