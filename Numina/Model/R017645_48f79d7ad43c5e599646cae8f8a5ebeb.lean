import Mathlib

theorem algebra_320121 {a b c : ℝ} (ha : a ≠ 0) (hroots : ∃ x1 x2, x1 ≠ x2 ∧ a * x1^2 + b * x1 + c = 0 ∧ a * x2^2 + b * x2 + c = 0 ∧ x1 / x2 = 2 / 3) :
    6 * b^2 = 25 * a * c := by
  rcases hroots with ⟨x1, x2, hx1x2, h1, h2, h3⟩
  have hx2ne0 : x2 ≠ 0 := by
    by_contra h
    rw [h] at h3
    norm_num at h3
    all_goals linarith
  have h4 : x1 = 2 / 3 * x2 := by
    field_simp [hx2ne0] at h3
    linarith
  rw [h4] at h1
  -- Subtract eq1 and eq2 to eliminate c
  have eq1 : a * ( (2/3 * x2)^2 ) + b * (2/3 * x2) + c = 0 := by linarith
  have eq2 : a * x2 ^ 2 + b * x2 + c = 0 := by linarith
  have eq3 : a * ( (2/3 * x2)^2 ) - a * x2^2 + b * (2/3 * x2) - b * x2 = 0 := by
    linarith [eq1, eq2]
  -- Multiply equation eq3 to clear denominators to get 5*a*x2^2 + 3*b*x2 = 0
  have eq4 : 5 * a * x2 ^ 2 + 3 * b * x2 = 0 := by
    nlinarith
  have eq5 : x2 * (5 * a * x2 + 3 * b) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq5) with h6 h7
  · -- Case x2 = 0 is impossible
    contradiction
  · -- Case 5*a*x2 + 3*b =0
    -- Substitute into h2 to get the final result
    have eq6 : 5 * a * x2 + 3 * b = 0 := by
      linarith
    have eq7 : 25 * a * c = 6 * b^2 := by
      have eq8 : x2 = (-3 * b) / (5 * a) := by
        field_simp [ha] at eq6 ⊢
        linarith
      rw [eq8] at eq2
      field_simp [ha] at eq2 ⊢
      nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (b), sq_nonneg (a * x2), sq_nonneg (x2)]
    linarith