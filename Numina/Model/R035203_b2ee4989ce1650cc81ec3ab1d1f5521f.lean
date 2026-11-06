import Mathlib

theorem algebra_319039 {f g : ℝ → ℝ} (hfg : ∀ x y, f (x - y) = f x * g y - g x * f y)
    (hf12 : f 1 = f 2) (hf2 : f 2 ≠ 0) : g 1 + g (-1) = 1 := by
  have h1 : f 0 = 0 := by
    specialize hfg 0 0
    norm_num at hfg
    linarith
  have h2 : g 0 = 1 := by
    have h3 : ∀ x : ℝ, f x * (1 - g 0) = 0 := by
      intro x
      specialize hfg x 0
      simp [h1] at hfg
      linarith
    have h4 := h3 2
    have h5 : f 2 * (1 - g 0) = 0 := by
      simpa using h4
    cases' (mul_eq_zero.mp h5) with h6 h7
    · contradiction
    · linarith
  have h3 : ∀ y : ℝ, f (-y) = -f y := by
    intro y
    specialize hfg 0 y
    simp [h1, h2] at hfg
    linarith
  have hf1 : f 1 ≠ 0 := by
    intro h
    have : f 2 = 0 := by 
      linarith [h, hf12]
    contradiction
  have h4 : f (1 - (-1)) = f 1 * g (-1) - g 1 * f (-1) := by
    apply hfg
  have h5 : f 2 = f 1 * g (-1) - g 1 * f (-1) := by
    rw [show (1 - (-1) : ℝ) = (2 : ℝ) by norm_num] at h4
    linarith
  -- rewrite f 2 = f 1 and f (-1) = -f 1
  have h6 : f (-1) = -f 1 := by
    specialize h3 1
    norm_num at h3 ⊢
    linarith
  rw [h6] at h5
  rw [show f 2 = f 1 by linarith [hf12]] at h5
  have h7 : f 1 * (1 - (g (-1) + g 1)) = 0 := by
    linarith
  cases' (mul_eq_zero.mp h7) with h8 h9
  · contradiction -- f 1 ≠ 0
  · linarith