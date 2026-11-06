import Mathlib

theorem algebra_255634 {x y z : ℝ} (h1 : x + y = z) (h2 : x^2 + y^2 = z) (h3 : x^3 + y^3 = z) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = 2) := by
  have h4 : z = x + y := by linarith
  rw [h4] at h2 h3
  have h5 : x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by
    ring
  rw [h5] at h3
  by_cases h : x + y = 0
  · -- Case where x + y = 0
    have h6 : x = 0 := by
      have h7 : x + y = 0 := by linarith
      have h8 : x^2 + y^2 = 0 := by nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
      have h9 : x^2 ≥ 0 := sq_nonneg x
      have h10 : y^2 ≥ 0 := sq_nonneg y
      have h11 : x^2 = 0 := by nlinarith
      have hx : x = 0 := pow_eq_zero h11
      linarith
    have h7 : y = 0 := by
      nlinarith [h, h6]
    have h8 : z = 0 := by
      nlinarith [h1, h6, h7]
    left
    exact ⟨by linarith, by linarith, by linarith⟩
  · -- Case where x + y ≠ 0
    have h6 : x^2 - x * y + y^2 = 1 := by
      apply (mul_left_inj' h).mp
      linarith
    have h7 : x * y = x + y - 1 := by
      nlinarith [h2, h6]
    have h9 : (x + y - 1) * (x + y - 2) = 0 := by
      nlinarith [h7, sq_nonneg (x - y)]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case where x + y = 1
      have h12 : x + y = 1 := by linarith
      have h13 : x * y = 0 := by
        nlinarith [h12, h7]
      cases' (mul_eq_zero.mp h13) with h14 h15
      · -- Case where x = 0
        have hx : x = 0 := h14
        have hy : y = 1 := by linarith [h12, hx]
        have hz : z = 1 := by
          nlinarith [h4, hx, hy]
        right
        left
        exact ⟨by linarith, by linarith, by linarith⟩
      · -- Case where y = 0
        have hy : y = 0 := h15
        have hx : x = 1 := by linarith [h12, hy]
        have hz : z = 1 := by
          nlinarith [h4, hx, hy]
        right
        right
        left
        exact ⟨by linarith, by linarith, by linarith⟩
    · -- Case where x + y = 2
      have h16 : x + y = 2 := by linarith
      have h17 : x * y = 1 := by
        nlinarith [h16, h7]
      have hx1 : x = 1 := by
        have h18 : (x - 1)^2 = 0 := by
          nlinarith [sq_nonneg (x - y), h16, h17]
        have hx1 : x - 1 = 0 := by
          nlinarith
        linarith
      have hy1 : y = 1 := by
        nlinarith [h16, hx1]
      have hz : z = 2 := by
        nlinarith [h4, hx1, hy1]
      right
      right
      right
      exact ⟨by linarith, by linarith, by linarith⟩