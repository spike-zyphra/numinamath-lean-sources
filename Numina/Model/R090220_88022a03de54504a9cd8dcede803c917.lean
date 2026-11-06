import Mathlib

theorem algebra_63120 {x y : ℝ} (h₀ : x ^ 2 + y ^ 2 = 2) (h₁ : x ^ 2 / (2 - y) + y ^ 2 / (2 - x) = 2) :
    (x, y) = (1, 1) := by
  have h2 : 2 - y ≠ 0 := by
    by_contra h
    have hy : y = 2 := by linarith
    rw [hy] at h₀
    nlinarith
  have h3 : 2 - x ≠ 0 := by
    by_contra h
    have hx : x = 2 := by linarith
    rw [hx] at h₀
    nlinarith
  have h4 : x ^ 2 * (2 - x) + y ^ 2 * (2 - y) = 2 * (2 - y) * (2 - x) := by
    have eq1 : x ^ 2 / (2 - y) + y ^ 2 / (2 - x) = 2 := h₁
    field_simp [h2, h3] at eq1 ⊢
    nlinarith
  have h5 : x = y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), h₀]
  have h6 : x ^ 2 = 1 := by
    have h7 : x = y := h5
    have h8 : x ^ 2 + x ^ 2 = 2 := by
      rw [show y = x by linarith [h7]] at h₀
      nlinarith
    nlinarith
  have hx1 : x = 1 ∨ x = -1 := by
    have h10 : x ^ 2 = 1 := h6
    rw [sq_eq_one_iff] at h10
    exact h10
  rcases hx1 with hx | hx
  · -- Case x = 1, then y = 1
    have hy : y = 1 := by
      nlinarith [h5, hx]
    simp [hx, hy]
  · -- Case x = -1, then y = -1, but contradicts h₁
    have hy : y = -1 := by
      nlinarith [h5, hx]
    rw [show y = -1 by linarith [hy]] at h₁
    rw [show x = -1 by linarith [hx]] at h₁
    norm_num at h₁
    all_goals
      norm_num at h₁ <;> try contradiction