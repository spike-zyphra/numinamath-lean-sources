import Mathlib

theorem algebra_166255 {x y : ℝ} (h1 : x^3 + y^3 = 19) (h2 : x^2 * y + x * y^2 = -6) :
    (x, y) = (-2, 3) ∨ (x, y) = (3, -2) := by
  have h1' : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by 
    ring_nf
  rw [h1'] at h1
  have h2' : x * y * (x + y) = -6 := by
    nlinarith
  have h3 : (x + y) ^ 3 = 1 := by
    have h1_subst : (x + y) ^ 3 - 3 * (x * y) * (x + y) = 19 := by 
      linarith
    have h4 : 3 * (x * y) * (x + y) = -18 := by
      have h_subst : x * y * (x + y) = -6 := by 
        nlinarith
      nlinarith [h_subst]
    nlinarith [h1_subst, h4, h2']
  have h6 : x + y = 1 := by
    have h7 : (x + y) ^ 3 - 1 = 0 := by linarith
    have h8 : (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) = 0 := by
      ring_nf at h7 ⊢
      linarith [h7]
    cases' mul_eq_zero.mp h8 with h9 h10
    · -- Case $x + y - 1 = 0$ implies $x + y = 1$
      linarith
    · -- Case $(x + y) ^ 2 + (x + y) + 1 = 0$
      have h8_pos : (x + y) ^ 2 + (x + y) + 1 > 0 := by
        nlinarith [sq_nonneg (x + y + 1 / 2)]
      have h8_zero : (x + y) ^ 2 + (x + y) + 1 = 0 := by
        nlinarith
      linarith [h8_pos, h8_zero]
  have hxy : x * y = -6 := by
    have : x * y = -6 := by
      rw [h6] at h2'
      have : x * y * 1 = -6 := by
        nlinarith
      linarith
    assumption
  have h7 : x ^ 2 - x - 6 = 0 := by
    have h8 : y = 1 - x := by
      linarith [h6]
    have : x * y = -6 := by
      nlinarith [hxy]
    nlinarith [sq_nonneg (x * y), sq_nonneg (x - 3), sq_nonneg (x + 2)]
  have h8 : (x - 3) * (x + 2) = 0 := by 
    nlinarith [h7]
  cases' mul_eq_zero.mp h8 with h9 h10
  · -- Case $x - 3 = 0$, so $x = 3$
    have hx1 : x = 3 := by linarith
    have hy1 : y = -2 := by linarith [h6, hx1]
    right
    simp [hx1, hy1]
  · -- Case $x + 2 = 0$, so $x = -2$
    have hx2 : x = -2 := by linarith
    have hy2 : y = 3 := by linarith [h6, hx2]
    left
    simp [hx2, hy2]
  all_goals
  nlinarith
  all_goals tauto
  all_goals tauto