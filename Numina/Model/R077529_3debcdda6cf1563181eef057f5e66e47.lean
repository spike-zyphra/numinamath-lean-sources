import Mathlib

theorem algebra_187029 {x y : ℝ} (h₀ : x / y + y / x = 13 / 6) (h₁ : x + y = 5) :
    (x, y) = (2, 3) ∨ (x, y) = (3, 2) := by 
  have h2 : x ≠ 0 := by
    by_contra h
    have h3 : x = 0 := h
    have h4 : y = 5 := by linarith [h₁, h3]
    rw [h3, h4] at h₀
    norm_num at h₀
  have h3 : y ≠ 0 := by
    by_contra h
    have h4 : y = 0 := h
    have h5 : x = 5 := by linarith [h₁, h4]
    rw [h5, h4] at h₀
    norm_num at h₀
  have h4 : x * y ≠ 0 := by
    apply mul_ne_zero
    exact h2
    exact h3
  have h5 : x ^ 2 + y ^ 2 = (13 / 6) * (x * y) := by
    have h6 : x / y + y / x = 13 / 6 := h₀
    field_simp [h2, h3] at h6 ⊢
    nlinarith
  have h7 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring
  rw [h₁] at h7
  rw [h7] at h5
  have h8 : x * y = 6 := by
    nlinarith
  have h9 : x = 2 ∨ x = 3 := by
    have h10 : x + y = 5 := h₁
    have h11 : x * y = 6 := h8
    have h12 : y = 5 - x := by linarith
    rw [h12] at h11
    have h13 : x ^ 2 - 5 * x + 6 = 0 := by
      nlinarith
    have h14 : (x - 2) * (x - 3) = 0 := by 
      nlinarith [h13]
    cases (mul_eq_zero.mp h14) with
    | inl h15 =>
      left
      linarith
    | inr h16 =>
      right
      linarith
  cases h9 with
  | inl hx =>
    have hy : y = 3 := by
      nlinarith
    left
    exact Prod.ext hx hy
  | inr hx =>
    have hy : y = 2 := by
      nlinarith
    right
    exact Prod.ext hx hy