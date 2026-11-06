import Mathlib

theorem algebra_199211 {x y z : ℝ} (h1 : x + y - z = 1) (h2 : x^2 - y^2 + z^2 = 1)
    (h3 : -x^3 + y^3 + z^3 = -1) :
    (x, y, z) = (0, 0, -1) ∨ (x, y, z) = (1, 0, 0) := by
  have h4 : z = x + y - 1 := by
    linarith
  rw [h4] at h2
  have h6 : x^2 + x * y - x - y = 0 := by
    nlinarith
  have h7 : (x + y) * (x - 1) = 0 := by
    nlinarith [h6]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case x + y = 0
    have h10 : y = -x := by linarith
    have h11 : z = -1 := by
      nlinarith [h4, h10]
    have h12 : x = 0 := by
      rw [h10, h11] at h3
      ring_nf at h3
      have h13 : x^3 = 0 := by
        nlinarith
      have h14 : x = 0 := by
        have h15 : x^3 = 0 := h13
        simp at h15 ⊢
        <;> nlinarith
      linarith
    have h17 : y = 0 := by
      nlinarith [h10, h12]
    have h18 : z = -1 := h11
    left
    simp [h12, h17, h18]
  · -- Case x - 1 = 0 ⇒ x = 1
    have h19 : x = 1 := by linarith
    have h20 : z = y := by
      nlinarith [h4, h19]
    have h21 : y = 0 := by
      rw [h19, show z = y by linarith] at h3
      ring_nf at h3
      have h22 : y^3 = 0 := by
        nlinarith
      have h23 : y = 0 := by
        have h24 : y^3 = 0 := h22
        simp at h24 ⊢
        <;> nlinarith
      linarith
    have h24 : z = 0 := by
      linarith [h20, h21]
    right
    simp [h19, h21, h24]