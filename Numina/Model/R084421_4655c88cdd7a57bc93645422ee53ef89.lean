import Mathlib

theorem algebra_11381 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y + 6 * x * y) (h' : f (-1) * f 1 ≥ 9) :
    f (2 / 3) = 4 / 3 := by
  have h0 : f 0 = 0 := by
    specialize h 0 0
    norm_num at h
    linarith
  have h1 : ∀ x, f (-x) = -f x + 6 * x ^ 2 := by
    intro x
    specialize h x (-x)
    simp [h0] at h
    linarith
  have h2 : f (-1) = -f 1 + 6 * (1 : ℝ) ^ 2 := by
    apply h1
  rw [h2] at h'
  have h3 : f 1 = 3 := by
    nlinarith [sq_nonneg (f 1 - 3)]
  have h4 : f (1 / 3 + 1 / 3) = f (1 / 3) + f (1 / 3) + 6 * (1 / 3) * (1 / 3) := by
    apply h
  have h5 : f (1 / 3 + 1 / 3) = 2 * f (1 / 3) + (2 / 3 : ℝ) := by
    linarith
  have h6 : f 1 = f (1 / 3 + 1 / 3) + f (1 / 3) + 6 * (1 / 3 + 1 / 3) * (1 / 3) := by
    rw [←h]
    ring_nf
    all_goals linarith
  rw [h5] at h6
  have h7 : f (1 / 3) = 1 / 3 := by
    linarith [h3, h6]
  have h8 : f (2 / 3) = 2 * f (1 / 3) + (2 / 3 : ℝ) := by
    specialize h (1 / 3) (1 / 3)
    norm_num at h ⊢
    linarith
  rw [h7] at h8
  linarith