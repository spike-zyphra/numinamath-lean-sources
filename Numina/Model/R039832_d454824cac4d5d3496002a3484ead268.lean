import Mathlib

theorem algebra_268201:
  {(x, y) : ℝ × ℝ | x^3 + y^3 = 26 ∧ x * y * (x + y) = -6} = {(-1, 3), (3, -1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is in the left side, prove it is in the right side
    rintro ⟨h1, h2⟩
    have h3 : (x + y) ^ 3 = 8 := by
      have eq1 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y * (x + y)) := by
        ring
      rw [eq1] at h1
      linarith [h1, h2]
    have h4 : x + y = 2 := by
      have h5 : (x + y) ^ 3 - 8 = 0 := by linarith
      have h6 : (x + y - 2) * ((x + y) ^ 2 + 2 * (x + y) + 4) = 0 := by 
        ring_nf at h5 ⊢
        linarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- x + y - 2 = 0
        linarith
      · -- (x + y) ^ 2 + 2 * (x + y) + 4 = 0
        have h9 : (x + y) ^ 2 + 2 * (x + y) + 4 = 0 := by linarith
        nlinarith [sq_nonneg ((x + y) + 1)]
    have h5 : x * y = -3 := by
      have h6 : x * y * (x + y) = -6 := h2
      rw [h4] at h6
      linarith
    have h8 : (x - 3) * (x + 1) = 0 := by
      have h9 : x + y = 2 := h4
      have h10 : y = 2 - x := by linarith
      rw [h10] at h5
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- x - 3 = 0
      have hx : x = 3 := by linarith
      have hy : y = -1 := by linarith [h4, hx]
      right
      simp [hx, hy]
    · -- x + 1 = 0
      have hx : x = -1 := by linarith
      have hy : y = 3 := by linarith [h4, hx]
      left
      simp [hx, hy]
  · -- Show that (-1, 3) and (3, -1) satisfy the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (-1, 3)
      constructor
      · norm_num
      · norm_num
    · -- (3, -1)
      constructor
      · norm_num
      · norm_num