import Mathlib

theorem algebra_324029 {f : ℝ → ℝ} (h : ∀ x y, (f x * f y - f (x * y)) / 3 = x + y + 2) :
    f 36 = 39 := by
  have h1 := h 0 0
  norm_num at h1
  have h2 : f 0 ^ 2 - f 0 - 6 = 0 := by linarith
  have h3 : f 0 = 3 ∨ f 0 = -2 := by
    have h4 : f 0 ^ 2 - f 0 - 6 = 0 := h2
    have h5 : (f 0 - 3) * (f 0 + 2) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · left
      linarith
    · right
      linarith
  cases h3 with
  | inl h4 =>
    have h5 : ∀ (y : ℝ), f y = y + 3 := by
      intro y
      have h1 := h 0 y
      norm_num [h4] at h1
      nlinarith
    specialize h5 36
    norm_num at h5 ⊢
    linarith
  | inr h4 =>
    have h51 : f 1 = -7 / 2 := by
      have h11 := h 0 1
      norm_num [h4] at h11
      nlinarith
    have h11 := h 1 1
    rw [h51] at h11
    norm_num at h11 
    all_goals
      linarith [h11]