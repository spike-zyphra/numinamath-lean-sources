import Mathlib

theorem algebra_244952 (x y : ℝ) (h1 : x^2 + x * y + y^2 = 37) (h2 : x^4 + x^2 * y^2 + y^4 = 481) :
    (x = -4 ∧ y = -3) ∨ (x = -3 ∧ y = -4) ∨ (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) := by
  have eq1 : x^4 + x^2 * y^2 + y^4 = (x^2 + x * y + y^2) * (x^2 - x * y + y^2) := by
    ring_nf
  rw [eq1] at h2
  rw [h1] at h2
  have h3 : x^2 - x * y + y^2 = 13 := by
    nlinarith
  have h4 : x * y = 12 := by
    nlinarith [h1, h3]
  have h5 : x^2 + y^2 = 25 := by
    nlinarith [h1, h4]
  have h6 : (x + y)^2 = 49 := by
    nlinarith [h5, h4]
  have h7 : x + y = 7 ∨ x + y = -7 := by
    have h : (x + y)^2 - 49 = 0 := by linarith
    have h8 : (x + y - 7) * (x + y + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · left
      linarith
    · right
      linarith
  cases' h7 with h7 h7
  · -- Case where x + y = 7
    have h8 : x + y = 7 := h7
    have hy : y = 7 - x := by linarith
    rw [hy] at h4
    have h9 : x^2 - 7 * x + 12 = 0 := by
      nlinarith
    have h10 : (x - 3) * (x - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with hx1 hx2
    · -- x - 3 = 0, so x = 3, y = 4
      have hx : x = 3 := by linarith
      have hy : y = 4 := by
        rw [hx] at hy
        linarith
      norm_num [hx, hy]
    · -- x - 4 = 0, so x = 4, y = 3
      have hx : x = 4 := by linarith
      have hy : y = 3 := by
        rw [hx] at hy
        linarith
      norm_num [hx, hy]
  · -- Case where x + y = -7
    have h8 : x + y = -7 := h7
    have hy : y = -7 - x := by linarith
    rw [hy] at h4
    have h9 : x^2 + 7 * x + 12 = 0 := by
      nlinarith
    have h10 : (x + 3) * (x + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with hx1 hx2
    · -- x + 3 = 0, so x = -3, y = -4
      have hx : x = -3 := by linarith
      have hy : y = -4 := by
        rw [hx] at hy
        linarith
      norm_num [hx, hy]
    · -- x + 4 = 0, so x = -4, y = -3
      have hx : x = -4 := by linarith
      have hy : y = -3 := by
        rw [hx] at hy
        linarith
      norm_num [hx, hy]