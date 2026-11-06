import Mathlib

theorem algebra_173953 (x y : ℝ) 
    (h1 : x^3 + y^3 + 3 * x * y = 1) (h2 : x^2 - y^2 = 1) :
    ((0 ≤ x ∧ 0 ≤ y) ∨ (0 < x + y)) → (x, y) = (1, 0) := by
  intro h3
  cases h3 with
  | inl h_nonneg =>
    rcases h_nonneg with ⟨hx, hy⟩
    have h3 : (x + y) ^ 3 = 1 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y), sq_nonneg (x + y - 1), sq_nonneg (x - y)]
    have h4 : x + y = 1 := by
      have h5 : (x + y) ^ 3 - 1 = 0 := by
        linarith
      have h6 : (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) = 0 := by
        ring_nf at h5 ⊢
        nlinarith 
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case where $x + y - 1 = 0$, so $x + y = 1$.
        linarith
      · -- Case where $(x + y)^2 + (x + y) + 1 = 0$.
        nlinarith [sq_nonneg ((x + y) + 1 / 2)]
    have h8 : x - y = 1 := by
      nlinarith [h4, h2]
    have hx1 : x = 1 := by
      nlinarith [h4, h8]
    have hy0 : y = 0 := by
      nlinarith [h4, h8]
    simp [hx1, hy0]
  | inr h_pos =>
    have h3 : (x + y) ^ 3 = 1 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y), sq_nonneg (x + y - 1), sq_nonneg (x - y)]
    have h4 : x + y = 1 := by
      have h5 : (x + y) ^ 3 - 1 = 0 := by
        linarith
      have h6 : (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) = 0 := by 
        ring_nf at h5 ⊢
        nlinarith 
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case where $x + y - 1 = 0$, so $x + y = 1$.
        linarith
      · -- Case where $(x + y)^2 + (x + y) + 1 = 0$.
        nlinarith [sq_nonneg ((x + y) + 1 / 2)]
    have h8 : x - y = 1 := by
      nlinarith [h4, h2]
    have hx1 : x = 1 := by
      nlinarith [h4, h8]
    have hy0 : y = 0 := by
      nlinarith [h4, h8]
    simp [hx1, hy0]