import Mathlib

theorem algebra_313650 {f : ℝ → ℝ} (h : ∀ x y, f (x ^ 3) + f (y ^ 3) = (x + y) * f (x ^ 2) + f (y ^ 2) - f (x * y)) :
    ∀ x, f x = 0 := by
  have h1 := h 0 0
  have f0 : f 0 = 0 := by
    norm_num at h1
    linarith

  have hfx1 : ∀ x : ℝ, f (x ^ 3) = x * f (x ^ 2) := by
    intro x
    specialize h x 0
    simp [show f 0 = 0 by linarith [f0]] at h
    linarith

  have hfx3 : ∀ y : ℝ, f (y ^ 3) = f (y ^ 2) := by
    intro y
    specialize h 0 y
    simp [show f 0 = 0 by linarith [f0]] at h
    linarith

  have eq1 : ∀ y : ℝ, f (y ^ 2) = y * f (y ^ 2) := by
    intro y
    have eq_a := hfx1 y
    have eq_b := hfx3 y
    have eq2 : f (y ^ 3) = f (y ^ 2) := eq_b
    have eq3 : f (y ^ 3) = y * f (y ^ 2) := eq_a
    linarith [eq2, eq3]

  have h3 : ∀ y : ℝ, f (y ^ 2) = 0 := by
    intro y
    have eq10 := eq1 y
    have eq11 := eq1 (-y)
    have : (-y : ℝ) ^ 2 = y ^ 2 := by ring
    rw [this] at eq11
    have h_eq1 : f (y ^ 2) = y * f (y ^ 2) := by
      linarith [eq10]
    have h_eq2 : f (y ^ 2) = -y * f (y ^ 2) := by
      linarith [eq11]
    nlinarith [h_eq1, h_eq2]

  have h5 : ∀ y : ℝ, f (y ^ 3) = 0 := by
    intro y
    have h6 : f (y ^ 3) = f (y ^ 2) := hfx3 y
    have h7 : f (y ^ 2) = 0 := h3 y
    rw [h7] at h6
    linarith

  have hx_zero_xy : ∀ x y : ℝ, f (x * y) = 0 := by
    intro x y
    specialize h x y
    have hx0 : f (x ^ 3) = 0 := h5 x
    have hy0 : f (y ^ 3) = 0 := h5 y
    have hx2 : f (x ^ 2) = 0 := h3 x
    have hy2 : f (y ^ 2) = 0 := h3 y
    simp [hx0, hy0, hx2, hy2] at h
    linarith

  intro x
  specialize hx_zero_xy x 1
  norm_num at hx_zero_xy
  linarith