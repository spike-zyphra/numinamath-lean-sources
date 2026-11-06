import Mathlib

theorem algebra_79028 {x y z : ℝ} (hxy : x ≠ 1 ∧ y ≠ 1) (hxy' : x ≠ y)
    (h : (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y)) :
    (y * z - x ^ 2) / (1 - x) = x + y + z ∧ (x * z - y ^ 2) / (1 - y) = x + y + z := by
  rcases hxy with ⟨hx1, hy1⟩
  have h1 : x - 1 ≠ 0 := by
    intro h2
    apply hx1
    linarith
  have h2 : y - 1 ≠ 0 := by
    intro h3
    apply hy1
    linarith
  have h1x : (1 - x) ≠ 0 := by
    intro h10
    apply hx1
    linarith
  have h1y : (1 - y) ≠ 0 := by
    intro h10
    apply hy1
    linarith
  have eq1 : (y * z - x ^ 2) * (1 - y) = (x * z - y ^ 2) * (1 - x) := by
    field_simp [h1x, h1y] at h ⊢
    nlinarith [h, sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by
      intro h3
      apply hx1
      linarith
    ), sq_pos_of_ne_zero (show (y - 1 : ℝ) ≠ 0 by
      intro h3
      apply hy1
      linarith
    ), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h3
      apply hxy'
      linarith
    ) ]
  constructor
  · -- Show that the first fraction is equal to x + y + z
    have h_eq1 : (y * z - x ^ 2) / (1 - x) = x + y + z := by
      have eq2 : (y * z - x ^ 2) = (x + y + z) * (1 - x) := by
        nlinarith [sq_pos_of_ne_zero (show (1 - x : ℝ) ≠ 0 by
          exact h1x
        ), sq_pos_of_ne_zero (show (1 - y : ℝ) ≠ 0 by
          exact h1y
        ), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
          intro h'
          apply hxy'
          linarith
        ), sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by
          intro h'
          apply hx1
          linarith
        ), sq_pos_of_ne_zero (show (y - 1 : ℝ) ≠ 0 by
          intro h'
          apply hy1
          linarith
        ), sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      rw [eq2]
      field_simp [h1x]
    exact h_eq1
  · -- Show that the second fraction is equal to x + y + z
    have h_eq2 : (x * z - y ^ 2) / (1 - y) = x + y + z := by
      have eq3 : (x * z - y ^ 2) = (x + y + z) * (1 - y) := by
        nlinarith [sq_pos_of_ne_zero (show (1 - x : ℝ) ≠ 0 by
          exact h1x
        ), sq_pos_of_ne_zero (show (1 - y : ℝ) ≠ 0 by
          exact h1y
        ), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
          intro h'
          apply hxy'
          linarith
        ), sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by
          intro h'
          apply hx1
          linarith
        ), sq_pos_of_ne_zero (show (y - 1 : ℝ) ≠ 0 by
          intro h'
          apply hy1
          linarith
        ), sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      rw [eq3]
      field_simp [h1y]
    exact h_eq2