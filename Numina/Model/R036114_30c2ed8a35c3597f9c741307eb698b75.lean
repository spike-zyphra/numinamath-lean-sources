import Mathlib

theorem algebra_165581 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ -2 ∧ x ≠ -3 ∧ x ≠ -4) :
    ((x - 1) * (x - 2) * (x - 3) * (x - 4)) / ((x + 1) * (x + 2) * (x + 3) * (x + 4)) = 1 ↔ x = 0 := by
  constructor
  · -- Forward: if the equation holds, then x = 0
    intro h
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    have h1 : (x + 1) * (x + 2) * (x + 3) * (x + 4) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      apply mul_ne_zero
      · -- x + 1 ≠ 0
        intro h1
        apply hx1
        linarith
      · -- x + 2 ≠ 0
        intro h2
        apply hx2
        linarith
      · -- x + 3 ≠ 0
        intro h3
        apply hx3
        linarith
      · -- x + 4 ≠ 0
        intro h4
        apply hx4
        linarith
    have h_eq : (x - 1) * (x - 2) * (x - 3) * (x - 4) = (x + 1) * (x + 2) * (x + 3) * (x + 4) := by
      field_simp [h1] at h
      linarith
    have h2 : x = 0 := by
      have eq1 : (x - 1) * (x - 2) * (x - 3) * (x - 4) - (x + 1) * (x + 2) * (x + 3) * (x + 4) = 0 := by 
        linarith [h_eq]
      have eq2 : x * (2 * x ^ 2 + 10) = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 5 * x), sq_nonneg (x ^ 2 + 5 * x), sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num)]
      cases' (mul_eq_zero.1 eq2) with eq3 eq4
      · -- Case x = 0 
        linarith
      · -- Case 2 * x ^ 2 + 10 = 0 
        nlinarith [sq_nonneg x]
    exact h2
  · -- Backward: if x = 0, then the equation holds
    intro h_eq
    rw [h_eq]
    norm_num