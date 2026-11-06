import Mathlib

theorem algebra_252199 (x y : ℝ) :
    x + y + x * y = 11 ∧ x ^ 2 + x * y + y ^ 2 = 19 ↔
    (x = 3 ∧ y = 2) ∨ (x = 2 ∧ y = 3) := by
  constructor
  · -- Assume the equations and derive the solutions
    rintro ⟨h₁, h₂⟩
    have h3 : (x + y) = 11 - x * y := by linarith
    have h4 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      ring
    have h5 : (x ^ 2 + y ^ 2) + (x * y) = 19 := by
      nlinarith
    rw [h4] at h5
    rw [h3] at h5
    have h6 : (x * y) ^ 2 - 23 * (x * y) + 102 = 0 := by
      nlinarith
    have h7 : (x * y - 6) * (x * y - 17) = 0 := by
      nlinarith [h6]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case 1: \( x \cdot y = 6 \)
      have h10 : x * y = 6 := by linarith
      have h11 : x + y = 5 := by linarith [h3, h10]
      have h12 : (x - 2) * (x - 3) = 0 := by
        have h_y : y = 5 - x := by linarith
        rw [h_y] at h10
        nlinarith
      cases' (mul_eq_zero.mp h12) with h13 h14
      · -- Case x = 2
        have hx1 : x = 2 := by linarith
        have hy1 : y = 3 := by linarith [h11, hx1]
        right
        exact ⟨hx1, hy1⟩
      · -- Case x = 3
        have hx2 : x = 3 := by linarith
        have hy2 : y = 2 := by linarith [h11, hx2]
        left
        exact ⟨hx2, hy2⟩
    · -- Case 2: \( x \cdot y = 17 \)
      have h14 : x * y = 17 := by linarith
      have h15 : x + y = -6 := by linarith [h3, h14]
      nlinarith [sq_nonneg (x - y)]
  · -- Show that the solutions satisfy the equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (3, 2)
      constructor
      · norm_num
      · norm_num
    · -- Check (2, 3)
      constructor
      · norm_num
      · norm_num