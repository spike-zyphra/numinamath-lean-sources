import Mathlib

theorem algebra_197127 (x y t z : ℝ) (h₀ : x * y - t ^ 2 = 9) (h₁ : x ^ 2 + y ^ 2 + z ^ 2 = 18) :
    (x, y, t, z) = (3, 3, 0, 0) ∨ (x, y, t, z) = (-3, -3, 0, 0) := by
  have h2 : z ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (t), sq_nonneg (z), sq_nonneg (x * y - 9)]
  have h3 : z = 0 := by
    nlinarith
  have h4 : x ^ 2 + y ^ 2 = 18 := by 
    rw [h3] at h₁
    nlinarith
  have h5 : t ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (t), sq_nonneg (z), sq_nonneg (x * y - 9)]
  have h6 : t = 0 := by
    nlinarith
  have h7 : x * y = 9 := by
    rw [h6] at h₀
    nlinarith
  have h8 : (x + y) ^ 2 = 36 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 9)]
  have h9 : x + y = 6 ∨ x + y = -6 := by
    have h : (x + y) ^ 2 = 36 := h8
    have : (x + y) = 6 ∨ (x + y) = -6 := by
      have h1 : (x + y) ^ 2 - 36 = 0 := by linarith
      have h2 : (x + y - 6) * (x + y + 6) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h2) with h3 h4
      · -- x + y - 6 = 0 
        left
        linarith
      · -- x + y + 6 = 0 
        right
        linarith
    assumption
  cases h9 with
  | inl h10 =>
    -- x + y = 6
    have h11 : (x - 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 9)]
    have h12 : x - 3 = 0 := by
      nlinarith
    have hx1 : x = 3 := by
      linarith
    have hy1 : y = 3 := by
      linarith
    left
    simp [hx1, hy1, h6, h3]
    <;> tauto
  | inr h11 =>
    -- x + y = -6
    have h13 : (x + 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 9)]
    have h14 : x + 3 = 0 := by
      nlinarith
    have hx2 : x = -3 := by
      linarith
    have hy2 : y = -3 := by
      linarith
    right
    simp [hx2, hy2, h6, h3]
    <;> tauto