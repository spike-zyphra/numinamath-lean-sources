import Mathlib

theorem algebra_213763 {f : ℝ → ℝ} (h : ∀ x y, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) :
    ∃ c, ∀ x, f x = c * x := by 
  -- Compute f(0)
  have h0 : f 0 = 0 := by 
    specialize h 0 0 
    norm_num at h 
    linarith 
  -- Show f(x^2) = x f(x)
  have h1 : ∀ x : ℝ, f (x ^ 2) = x * f x := by 
    intro x 
    specialize h x 0 
    simp [h0] at h 
    linarith 
  -- Show f is odd: f(-y) = -f(y)
  have h_odd : ∀ y : ℝ, f (-y) = - f y := by 
    intro y 
    have h2 := h 0 y 
    simp [h0] at h2 
    have h3 : f (y ^ 2) = y * f y := h1 y 
    have h6 : f (y ^ 2) = - y * f (-y) := by 
      specialize h1 (-y) 
      rw [show (-y) ^ 2 = y ^ 2 by ring] at h1 
      linarith 
    by_cases hy : y = 0 
    · 
      rw [hy] 
      simp [h0] 
    · 
      have h7 : y ≠ 0 := hy 
      have eq1 : y * f y = - y * f (-y) := by 
        linarith [h3, h6] 
      have eq2 : f y = - f (-y) := by 
        apply (mul_left_inj' h7).mp 
        linarith 
      linarith 
  -- Show that x f(y) = y f(x) for all x, y 
  have h2' : ∀ x y : ℝ, x * f y = y * f x := by 
    intro x y 
    have eq1 := h x (-y) 
    have eq2 := h x y 
    simp [show (-y) ^ 2 = y ^ 2 by ring, h_odd] at eq1 
    nlinarith [eq1, eq2] 
  -- Let c = f(1), then f(x) = c * x 
  use f 1 
  intro x 
  have h2 := h2' x 1 
  simp at h2 
  linarith