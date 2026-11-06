import Mathlib

theorem algebra_7038 {x y : ℝ} (hxpos : 0 < x) (hypos : 0 < y) (hxy : x ≠ y)
    (a b : ℝ) (ha : a = 1 / x) (hb : b = 1 / y) (h : (a + b) / (a - b) = 6) :
    2 * x / (y - x) = 5 := by

  have h1 : a - b ≠ 0 := by
    rw [ha, hb]
    have h2 : 1 / x - 1 / y ≠ 0 := by
      by_contra h3
      have h4 : 1 / x = 1 / y := by linarith
      have h5 : x = y := by
        field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)] at h4
        linarith
      contradiction
    exact h2

  have h2 : a + b = 6 * (a - b) := by
    have h2 : a - b ≠ 0 := h1
    field_simp [h2] at h
    linarith

  rw [ha, hb] at h2

  have h4 : x + y = 6 * (y - x) := by
    field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)] at h2 ⊢
    nlinarith [h2]

  have h5 : 7 * x = 5 * y := by
    linarith [h4]

  have h6 : y - x ≠ 0 := by
    intro h7
    apply hxy
    linarith

  have h7 : 2 * x = 10 / 7 * y := by
    linarith [h5]

  have h8 : y - x = 2 / 7 * y := by
    linarith [h5]

  have h9 : 2 * x / (y - x) = 5 := by
    rw [h7, h8]
    have hyne : y ≠ 0 := by linarith
    field_simp [hyne]
    <;> nlinarith
  exact h9